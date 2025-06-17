use std::{collections::HashSet, fs::{self, File}, io::{Read, Write}, path::{Path, PathBuf}};

use anyhow::{anyhow, Context, Result};
use chrono::{DateTime, Utc};
use glob::glob;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use tar::Builder;
use uuid::Uuid;

#[derive(Deserialize)]
pub struct Config {
    pub basic: Basic,
    pub snapshot: SnapshotConfig,
}

#[derive(Deserialize)]
pub struct Basic {
    pub version: String,
}

#[derive(Deserialize)]
pub struct SnapshotConfig {
    pub include: Vec<String>,
    pub include_large: Option<bool>,
    pub rng_seed: Option<u64>,
}

#[derive(Serialize)]
pub struct ManifestEntry {
    pub path: String,
    pub sha256: String,
}

#[derive(Serialize)]
pub struct Manifest {
    pub bourbaki_version: String,
    pub rng_seed: u64,
    pub run_started: DateTime<Utc>,
    pub container_digest: String,
    pub files: Vec<ManifestEntry>,
}

pub struct Snapshot;

impl Snapshot {
    pub fn create(config: &Config, container_digest: &str, output_dir: &Path) -> Result<String> {
        fs::create_dir_all(output_dir)?;
        let run_started = Utc::now();
        let include_large = config.snapshot.include_large.unwrap_or(false);
        let rng_seed = config.snapshot.rng_seed.unwrap_or(42);

        let mut files_set = HashSet::new();
        for pattern in &config.snapshot.include {
            for entry in glob(pattern)? {
                let path = entry?;
                if path.is_file() {
                    files_set.insert(path);
                }
            }
        }
        let mut files: Vec<PathBuf> = files_set.into_iter().collect();
        files.sort();

        let mut manifest_entries = Vec::new();
        for p in &files {
            let meta = fs::metadata(p)?;
            if meta.len() > 100_000_000 && !include_large {
                continue;
            }
            let mut f = File::open(p)?;
            let mut hasher = Sha256::new();
            std::io::copy(&mut f, &mut hasher)?;
            let hash = format!("{:x}", hasher.finalize());
            manifest_entries.push(ManifestEntry { path: p.to_string_lossy().to_string(), sha256: hash });
        }

        let manifest = Manifest {
            bourbaki_version: config.basic.version.clone(),
            rng_seed,
            run_started,
            container_digest: container_digest.to_string(),
            files: manifest_entries,
        };

        let uuid = Uuid::new_v4();
        let archive_path = output_dir.join(format!("{uuid}.tar.zst"));
        let tar_f = File::create(&archive_path)?;
        let enc = zstd::Encoder::new(tar_f, 0)?;
        let mut builder = Builder::new(enc.auto_finish());
        for p in &files {
            builder.append_path_with_name(p, p)?;
        }
        let manifest_json = serde_json::to_vec_pretty(&manifest)?;
        let mut header = tar::Header::new_gnu();
        header.set_path("manifest.json")?;
        header.set_size(manifest_json.len() as u64);
        header.set_cksum();
        builder.append(&header, manifest_json.as_slice())?;
        builder.finish()?;
        let enc = builder.into_inner()?;
        enc.finish()?;

        let mut f = File::open(&archive_path)?;
        let mut hasher = Sha256::new();
        std::io::copy(&mut f, &mut hasher)?;
        let archive_hash = format!("{:x}", hasher.finalize());
        println!("Snapshot SHA-256: {archive_hash}");
        Ok(archive_hash)
    }

    pub fn verify(archive: &Path) -> Result<()> {
        let file = File::open(archive)?;
        let dec = zstd::Decoder::new(file)?;
        let mut ar = tar::Archive::new(dec);
        let mut manifest_data = None;
        for entry in ar.entries()? {
            let mut e = entry?;
            let path = e.path()?.to_path_buf();
            if path == Path::new("manifest.json") {
                let mut buf = Vec::new();
                e.read_to_end(&mut buf)?;
                manifest_data = Some(buf);
                break;
            }
        }
        let manifest_data = manifest_data.ok_or_else(|| anyhow!("manifest missing"))?;
        let manifest: Manifest = serde_json::from_slice(&manifest_data)?;

        let file = File::open(archive)?;
        let dec = zstd::Decoder::new(file)?;
        let mut ar = tar::Archive::new(dec);
        let mut size: u64 = 0;
        for entry in ar.entries()? {
            let mut e = entry?;
            let path = e.path()?.to_path_buf();
            if path == Path::new("manifest.json") {
                continue;
            }
            if path.components().any(|c| matches!(c, std::path::Component::ParentDir)) {
                return Err(anyhow!("invalid path in archive"));
            }
            let mut buf = Vec::new();
            e.read_to_end(&mut buf)?;
            size += buf.len() as u64;
            let mut hasher = Sha256::new();
            hasher.update(&buf);
            let hash = format!("{:x}", hasher.finalize());
            let entry_str = path.to_string_lossy();
            let m = manifest.files.iter().find(|f| f.path == entry_str);
            if let Some(fm) = m {
                if fm.sha256 != hash {
                    return Err(anyhow!("hash mismatch for {}", fm.path));
                }
            } else {
                return Err(anyhow!("manifest missing entry for {}", entry_str));
            }
        }
        if size > 200_000_000 {
            return Err(anyhow!("archive uncompressed too large"));
        }
        Ok(())
    }
}

pub fn load_config(path: &Path) -> Result<Config> {
    let s = fs::read_to_string(path)?;
    let cfg: Config = toml::from_str(&s).context("parse config")?;
    Ok(cfg)
}
