use std::path::PathBuf;

use anyhow::Result;
use clap::{Parser, Subcommand};
use serde_json;
use snapshot::{load_config, Snapshot};

#[derive(Parser)]
#[command(author, version, about)]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    /// Container digest to record
    #[arg(long, default_value = "unknown")]
    container_digest: String,

    /// Output directory
    #[arg(long, default_value = "snapshots")]
    output: PathBuf,

    /// Path to config file
    #[arg(long, default_value = "bourbaki.toml")]
    config: PathBuf,
}

#[derive(Subcommand)]
enum Commands {
    Create,
    Verify { archive: PathBuf },
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Commands::Create => {
            let cfg = load_config(&cli.config)?;
            let hash = Snapshot::create(&cfg, &cli.container_digest, &cli.output)?;
            // update DAG root node with snapshot hash
            let dag_path = PathBuf::from("dag/dag_nodes.json");
            if dag_path.exists() {
                let mut data: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&dag_path)?)?;
                if let Some(root) = data.get_mut("thm:zero_encoding_general") {
                    root["snapshot_hash"] = serde_json::Value::String(hash.clone());
                    std::fs::write(&dag_path, serde_json::to_string_pretty(&data)?)?;
                }
            }
            println!("Created snapshot with hash {hash}");
        }
        Commands::Verify { archive } => {
            Snapshot::verify(&archive)?;
            println!("Snapshot verified");
        }
    }
    Ok(())
}
