#!/usr/bin/env python3

import argparse
import subprocess

ap = argparse.ArgumentParser()
ap.add_argument('murxla_binary')
args = ap.parse_args()

cmd = [args.murxla_binary, '-h']
completed = subprocess.run(cmd, capture_output=True)

with open('cli_options.rst', 'w') as outfile:
    outfile.write('.. code:: none\n\n')
    lines = completed.stdout.decode().split('\n')
    outfile.write('\n'.join('    ' + x for x in lines))
