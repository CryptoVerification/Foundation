"""Finite checks for the mathematical note, not a cryptographic implementation.

Run from the repository root:
    python3 docs/experiments/check_linear_cuts.py
"""

from collections import Counter
from fractions import Fraction
from itertools import product


def binary_rank(rows):
    """Rank over F_2, with rows represented by integer bit masks."""
    basis = {}
    for value in rows:
        while value:
            pivot = value.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = value
                break
            value ^= basis[pivot]
    return len(basis)


def evaluate(rows, value):
    return sum(
        ((row & value).bit_count() & 1) << index
        for index, row in enumerate(rows)
    )


def check_distributions():
    matrix_count = 0
    case_count = 0
    for output_bits in range(4):
        for input_bits in range(5):
            for rows in product(range(1 << input_bits), repeat=output_bits):
                matrix_count += 1
                for selected in range(1 << input_bits):
                    uniform_values = [
                        value for value in range(1 << input_bits)
                        if value & ~selected == 0
                    ]
                    fixed_values = [
                        value for value in range(1 << input_bits)
                        if value & selected == 0
                    ]
                    rank = binary_rank([row & selected for row in rows])
                    expected = 1 - Fraction(1 << rank, 1 << output_bits)
                    for fixed in fixed_values:
                        counts = Counter(
                            evaluate(rows, value ^ fixed)
                            for value in uniform_values
                        )
                        actual = sum(
                            (
                                abs(
                                    Fraction(counts[out], len(uniform_values))
                                    - Fraction(1, 1 << output_bits)
                                )
                                for out in range(1 << output_bits)
                            ),
                            Fraction(0),
                        ) / 2
                        assert actual == expected, (
                            rows, selected, fixed, actual, expected
                        )
                        assert (len(counts) == 1 << output_bits) == (
                            rank == output_bits
                        )
                        case_count += 1
    assert (matrix_count, case_count) == (5058, 370498)
    print(
        f"rank/uniformity/TV: {matrix_count} matrices; "
        f"{case_count} fixed-complement cases; all passed"
    )


def check_set_cover_encoding():
    case_count = 0
    for subsets in product(range(8), repeat=3):
        blocks = []
        columns = []
        for subset in subsets:
            start = len(columns)
            columns.extend(1 << bit for bit in range(3) if subset >> bit & 1)
            blocks.append(((1 << len(columns)) - 1) ^ ((1 << start) - 1))
        rows = tuple(
            sum(((col >> row) & 1) << index for index, col in enumerate(columns))
            for row in range(3)
        )
        for choice in range(8):
            union = 0
            column_mask = 0
            for index in range(3):
                if choice >> index & 1:
                    union |= subsets[index]
                    column_mask |= blocks[index]
            assert (
                binary_rank([row & column_mask for row in rows]) == 3
            ) == (union == 7)
            case_count += 1
    assert case_count == 4096
    print(f"set-cover encoding: {case_count} family/selection cases; all passed")


def check_examples():
    examples = [
        ("xor", (3,), [1, 2], [1, 2]),
        ("concat", (1, 2), [1, 2], [3]),
        ("shared-cancel", (0,), [1], []),
        ("shared-pair", (1, 1), [1], []),
    ]
    for name, rows, blocks, expected in examples:
        sufficient = []
        for choice in range(1 << len(blocks)):
            mask = 0
            for index, block in enumerate(blocks):
                if choice >> index & 1:
                    mask |= block
            if binary_rank([row & mask for row in rows]) == len(rows):
                sufficient.append(choice)
        minimal = [
            choice for choice in sufficient
            if not any(
                other != choice and other & choice == other
                for other in sufficient
            )
        ]
        assert minimal == expected, (name, minimal, expected)
        print(f"{name}: minimal source masks {minimal}")


if __name__ == "__main__":
    check_distributions()
    check_set_cover_encoding()
    check_examples()
