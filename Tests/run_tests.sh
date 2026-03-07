#!/bin/bash
# Run GeometricAlgebra paclet tests
# Usage: ./run_tests.sh [test_id_pattern]

set -euo pipefail

cd "$(dirname "$0")/.."

FILTER="${1:-}"

wolframscript -c "
PacletDirectoryLoad[\"GeometricAlgebra\"];
tr = TestReport[\"Tests/Tests.wlt\"];

passed = Length[Select[Values[tr[\"TestResults\"]], #[\"Outcome\"] === \"Success\" &]];
total = Length[tr[\"TestResults\"]];
failed = total - passed;

Print[\"\\n=== Test Results ===\"];
Print[\"Passed: \", passed, \"/\", total];
If[failed > 0, Print[\"Failed: \", failed]];
Print[];

Do[
    With[{t = tr[\"TestResults\"][i]},
        If[\"$FILTER\" === \"\" || StringContainsQ[t[\"TestID\"], \"$FILTER\", IgnoreCase -> True],
            Print[If[t[\"Outcome\"] === \"Success\", \"  ✓ \", \"  ✗ \"], t[\"TestID\"]];
            If[t[\"Outcome\"] =!= \"Success\",
                Print[\"    Expected: \", Short[t[\"ExpectedOutput\"], 2]];
                Print[\"    Actual:   \", Short[t[\"ActualOutput\"], 2]]
            ]
        ]
    ],
    {i, Keys[tr[\"TestResults\"]]}
];

Print[];
If[failed > 0,
    Print[\"FAILED\"];
    Exit[1],
    Print[\"ALL TESTS PASSED\"];
    Exit[0]
]
"
