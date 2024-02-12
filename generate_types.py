import json
import random

# Define the quantities of each item type
quantities = {'Character': 2500, 'Weapon': 3311, 'Armor': 3311, 'Potion': 777, 'Grail': 100}

seed = 0x06b553102c10676fe968b1c3636daee3a913724444d94d4329cac36d9e1de763
random.seed(seed)

# Create an array with item types repeated according to their quantities
items = []
for type, quantity in quantities.items():
    items.extend([type] * quantity)

# Shuffle the array randomly
random.shuffle(items)

for i, item in enumerate(items):
    # Create the JSON data
    data = {"type": item}

    # Define the file name
    filename = f"{i + 2}.json"

    # Write the JSON data to a file
    with open(filename, 'w') as f:
        json.dump(data, f, indent=2)
