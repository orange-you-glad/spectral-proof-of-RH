#!/bin/sh

set -eu

flatfile="source"
rm -f "$flatfile" included.tmp
touch "$flatfile" included.tmp

main_file="main.tex"
project_root=$(dirname "$(realpath "$main_file")")

echo "Building clean $flatfile..."

expand_tex() {
    file="$1"

    if ! [ -f "$file" ]; then
        echo "% Missing file: $file" >> "$flatfile"
        return
    fi

    real=$(realpath "$file")
    if grep -Fxq "$real" included.tmp; then
        echo "% Skipping duplicate: $file" >> "$flatfile"
        return
    fi
    echo "$real" >> included.tmp

    relpath=$(python3 -c "import os.path; print(os.path.relpath('$file', '$project_root'))")
    echo "% ===== Begin File: source/$relpath =====" >> "$flatfile"

    while IFS='' read -r line || [ -n "$line" ]; do
        trimmed="$(printf '%s' "$line" | sed -E 's/^[[:space:]]*//')"

        if printf '%s\n' "$trimmed" | grep -Eq '^\\(input|include)\{[^}]+\}'; then
            # Extract path inside braces
            included=$(printf '%s' "$trimmed" | sed -nE 's/^\\(input|include)\{([^}]+)\}/\2/p')
            [ -z "$included" ] && printf '%s\n' "$line" >> "$flatfile" && continue
            case "$included" in
                *.tex) texfile="$included" ;;
                *) texfile="${included}.tex" ;;
            esac
            full="$project_root/$texfile"
            if [ -f "$full" ]; then
                expand_tex "$full"
            else
                echo "% Missing or invalid include: $included" >> "$flatfile"
            fi
        else
            printf '%s\n' "$line" >> "$flatfile"
        fi
    done < "$file"

    echo "% ===== End File: source/$relpath =====" >> "$flatfile"
}

# Preamble header
{
    echo "% ===== Beginning linearized document ====="
} >> "$flatfile"

# Kick off recursive expansion from main.tex
expand_tex "$main_file"

echo "Successfully built $flatfile cleanly!"
