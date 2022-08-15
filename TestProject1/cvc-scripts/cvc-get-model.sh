#!/bin/bash

input="$1"
output="$2"

cvc -m "$input" > "$output"