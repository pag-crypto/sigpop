#!/bin/bash

ITERATIONS=5

# Define the possible values for DEPTH
DEPTH=(1 2 3 4 5 6 7 8 9 10 11 12 13 14)

# Define the path for the single output file
current_date=$(date +"%m-%d")
output_file="gk_$current_date.txt"


for dep in "${DEPTH[@]}"; do
    cargo build --release --example ecdsa_ring --features r1cs,smt,zok,bellman,datalog
    echo "Running ECDSA Ring signature with depth $dep" | tee -a "$output_file"
    for i in $(seq 1 $ITERATIONS); do
        # Prove step
        echo "Prove with depth $dep" | tee -a "$output_file"
        ./target/release/examples/ecdsa_ring --action prove --n "$dep" >> "$output_file" 2>&1
        
        # Verify step
        echo "Veriy with depth $dep" | tee -a "$output_file"
        ./target/release/examples/ecdsa_ring --action verify --n "$dep" >> "$output_file" 2>&1
    done
    ls -lh pi_gk | tee -a "$output_file"
    ls -lh st | tee -a "$output_file"
done

python3 scripts/python/bench/parse_ring.py
