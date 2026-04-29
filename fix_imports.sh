#!/bin/bash
cd /Users/buley/Documents/Code/emotions/open-source/gnosis-math

# Find all lean files in subdirectories of Gnosis
find Gnosis -mindepth 2 -name "*.lean" | while read -r file; do
    # Get the module path from the file path
    # e.g. Gnosis/Braided/BraidedTower.lean -> Gnosis.Braided.BraidedTower
    module_path=$(echo "$file" | sed 's/\.lean$//' | sed 's/\//\./g')
    
    # Get the old module path (as if it was in Gnosis/)
    # e.g. Gnosis.BraidedTower
    filename=$(basename "$file" .lean)
    old_module_path="Gnosis.$filename"
    
    # If the module path is different from the old one, we need to replace it
    if [ "$module_path" != "$old_module_path" ]; then
        echo "Replacing $old_module_path with $module_path"
        # Find all .lean files and replace the import
        grep -rl "import $old_module_path" . | xargs -r sed -i '' "s/import $old_module_path/import $module_path/g"
        # Also replace in Gnosis.lean (root module)
        # Gnosis.lean uses import Gnosis.X
        # Wait, grep already covers Gnosis.lean if it's in the current dir.
    fi
done
