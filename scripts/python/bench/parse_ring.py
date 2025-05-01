import re
import csv
from collections import defaultdict
from statistics import median
from datetime import datetime

def parse_data(file_path):
    # Initialize a defaultdict with list to store times for each depth
    result = defaultdict(lambda: {"prover": [], "verifier": []})

    # Read the data from the file
    with open(file_path, 'r') as file:
        data = file.read()

    # Regular expression to capture the depth and time values
    prove_pattern = re.compile(r"Prove with depth (\d+)\nTime for Proving: ([\d.]+)(ms|s)")
    verify_pattern = re.compile(r"Veriy with depth (\d+)\nTime for Verifying: ([\d.]+)ms")

    # Find all Proving times and their depths
    proves = prove_pattern.findall(data)
    # Find all Verifying times and their depths
    verifies = verify_pattern.findall(data)

    # Populate the result dict with proving times
    for depth, time, unit in proves:
        time_value = float(time)
        if unit == 's':
            time_value *= 1000
        result[int(depth)]["prover"].append(time_value)  # Store proving times

    # Populate the result dict with verifying times
    for depth, time in verifies:
        result[int(depth)]["verifier"].append(float(time))  # Store verifying times

    return dict(result)

def compute_stats(times):
    """Helper function to compute min, median, and max."""
    if not times:
        return (None, None, None)
    return (min(times), median(times), max(times))

def write_stats_to_csv(data, output_file):
    """Write the min, median, and max statistics to a CSV file."""
    with open(output_file, 'w', newline='') as csvfile:
        fieldnames = ['Depth', 'Prover Min', 'Prover Median', 'Prover Max', 
                      'Verifier Min', 'Verifier Median', 'Verifier Max']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()

        for depth, times in data.items():
            prover_stats = compute_stats(times['prover'])
            verifier_stats = compute_stats(times['verifier'])

            writer.writerow({
                'Depth': depth,
                'Prover Min': prover_stats[0],
                'Prover Median': prover_stats[1],
                'Prover Max': prover_stats[2],
                'Verifier Min': verifier_stats[0],
                'Verifier Median': verifier_stats[1],
                'Verifier Max': verifier_stats[2]
            })


if __name__ == "__main__":
    # Specify the path to the file containing the data
    today = datetime.today().strftime('%m-%d')
    subpath = f'{today}'
    file_path = 'gk_' + subpath + '.txt'
    output_file = 'ecdsa_ring_' + subpath + '.csv'  

    # Parse the data from the file
    parsed_data = parse_data(file_path)

    # Print the parsed dictionary
    print(parsed_data)

    write_stats_to_csv(parsed_data, output_file)

