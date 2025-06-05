Package["Wolfram`GeometricAlgebra`"]


PackageExport["MultivectorFunction"]
PackageExport["MultivectorPower"]
PackageExport["MultivectorExp"]
PackageExport["MultivectorLog"]
PackageExport["CanonicalGeometricAlgebra"]
PackageExport["CanonicalGeometricIndices"]
PackageExport["ConvertGeometricAlgebra"]
PackageExport["CanonicalMultivector"]
PackageExport["MultivectorMatrix"]
PackageExport["MatrixMultivector"]
PackageExport["MultivectorBlock"]
PackageExport["LeftKroneckerProduct"]
PackageExport["RightKroneckerProduct"]
PackageExport["DualComplexMultivector"]
PackageExport["ComplexDualMultivector"]

PackageScope["nilpotentBasis"]
PackageScope["nilpotentMatrix"]
PackageScope["multivectorBasisMatrix"]


Options[kroneckerProduct] = {"Direction" -> Left, "Flatten" -> True};

kroneckerProduct[va_MultivectorArray, wa_MultivectorArray, OptionsPattern[]] := With[{
    a = GeometricProduct[va, wa],
    r = va["Rank"],
    s1 = va["Shape"],
    s2 = wa["Shape"],
    dir = OptionValue["Direction"]
},
    If[ OptionValue["Flatten"],
        MultivectorArray[
            Flatten[If[dir === Left, Transpose[#, r <-> r + 1] &, Identity][a["Components"]], {{r, r + 1}}],
            Join[s1[[;; -2]], {If[dir === Left, Sign[s1[[-1]]], Sign[s2[[1]]]] Abs[s1[[-1]] s2[[1]]]}, s1[[2 ;;]]]
        ],
        MultivectorArray[
            If[dir === Left, Transpose[#, r <-> r + 1] &, Identity][a["Components"]],
            Join[s1, s2]
        ]
    ]
]

kroneckerProduct[va_MultivectorArray, OptionsPattern[]] := va

kroneckerProduct[vas__MultivectorArray, opts : OptionsPattern[]] := Fold[kroneckerProduct[##, opts] &, {vas}]

kroneckerProduct[OptionsPattern[]] := MultivectorArray[{Multivector[{1}, {0, 0}]}, {If[OptionValue["Direction"] === Left, - 1, 1]}]


LeftKroneckerProduct[vas___MultivectorArray] := kroneckerProduct[vas, "Direction" -> Left]

RightKroneckerProduct[vas___MultivectorArray] := kroneckerProduct[vas, "Direction" -> Right]


CanonicalGeometricAlgebra[g_GeometricAlgebra] := Block[{
    p, q, r, n, n1, n2, indexConversion, newIndex
},
    {p, q, r} = g["Signature"];
    n = p + q;
    n1 = Floor[n / 2];
    n2 = Ceiling[n / 2];
    indexConversion = CanonicalGeometricIndices[g];
    newIndex = Map[
        With[{c = indexConversion[#][[1]], index = geometricIndexFormat[g, #]},
            indexConversion[#][[2]] -> Switch[c,
                -1 | -I, Row[{"(", c, ")", index}],
                I, Row[{"\[ImaginaryI]", index}],
                _, index
            ]
        ] &,
        g["Indices"]
    ];
    GeometricAlgebra[{n1, n2, r}, "FormatIndex" -> newIndex]
]


CanonicalGeometricIndices[g_GeometricAlgebra] := Block[{
    n1, n2, p, q, r, n, complexIndices, newIndex
},
    {p, q, r} = g["Signature"];
    n = p + q;
    n1 = Floor[n / 2];
    n2 = Ceiling[n / 2];
    If[ p > q,
        complexIndices = Range[n1 + 1, p];
        newIndex = AssociationMap[index |-> (
            {
                #2 * (I ^ Count[index, _ ? (MemberQ[complexIndices, #] &)]),
                #1
            } & @@ orderIndexWithSign[Map[Which[# > p, # - (p - n1), MemberQ[complexIndices, #], # - n - 1, True, #] &, index], n + r])
            ,
            g["Indices"]
        ],
        complexIndices = Range[-n2 - 1, -q, -1];
        newIndex = AssociationMap[index |-> (
            {
                #2 * (I ^ Count[index, _ ? (MemberQ[complexIndices, #] &)]),
                #1
            } & @@ orderIndexWithSign[Map[Which[# > p, # - (p - n1), MemberQ[complexIndices, #], # + n + 1, True, #] &, index], n + r])
            ,
            g["Indices"]
        ]
    ];
    newIndex
]


Options[ConvertGeometricAlgebra] = {"Pseudoscalar" -> I};

ConvertGeometricAlgebra[
    v_Multivector,
    g_GeometricAlgebra,
    opts: OptionsPattern[ConvertGeometricAlgebra]] := Block[{
        h = GeometricAlgebra[v], toCanonicConversion, fromCanonicConversion, canonicCoordinates, i, w
},
    If[ h == g, Return[Multivector[v["Coordinates"], g]]];
    If[ v["ComplexDimension"] + 2 v["DualDimension"] != g["ComplexDimension"] + 2 g["DualDimension"],
        Return[Multivector[v, g]]
    ];
    If[ g["DualDimension"] > v["DualDimension"],
        Return[ConvertGeometricAlgebra[ComplexDualMultivector[v, g["DualDimension"] - v["DualDimension"]], g, opts]]
    ];
    If[ g["DualDimension"] < v["DualDimension"],
        Return[ConvertGeometricAlgebra[ComplexDualMultivector[DualComplexMultivector[v], g["DualDimension"]], g, opts]]
    ];
    toCanonicConversion = CanonicalGeometricIndices[v["GeometricAlgebra"]];
    fromCanonicConversion = CanonicalGeometricIndices[g];
    canonicCoordinates = Association @ MapThread[Function[{x, y}, y[[2]] -> x y[[1]]],
        {h["InverseBasisMatrix"] . v["Coordinates"], Values[toCanonicConversion]}
    ];
    i = OptionValue["Pseudoscalar"];

    w = Total @ KeyValueMap[
        With[{c = canonicCoordinates[#2[[2]]] Conjugate[#2[[1]]]},
            Multivector[<|#1 -> If[i != I, Re[c] + Im[c] i, c]|>, g]
        ] &,
        fromCanonicConversion
    ];

    Multivector[g["BasisMatrix"] . w["Coordinates"], g][Map[reduceFunctions]]
]

ConvertGeometricAlgebra[v_Multivector, args: Except[OptionsPattern[]], opts: OptionsPattern[]] :=
    ConvertGeometricAlgebra[v, GeometricAlgebra[args, FilterRules[{opts}, Options[GeometricAlgebra]]], opts]


CanonicalMultivector[v_Multivector, opts : OptionsPattern[]] :=
    ConvertGeometricAlgebra[
        v,
        GeometricAlgebra[CanonicalGeometricAlgebra[GeometricAlgebra[v]]["Signature"]],
        opts
    ]


fromRealCanonicalMultivector[v_Multivector, g_GeometricAlgebra] /;
    CanonicalGeometricAlgebra[v["GeometricAlgebra"]]["Signature"] == v["Signature"] :=
Block[{
    assoc, G, is, j
},
    G = v["GeometricAlgebra"];
    assoc = v["Association"];
    is = Association[
        # -> multiplyIndices[#, Last @ G["Indices"], G["Metric"]] & /@
        Cases[CanonicalGeometricIndices[g], HoldPattern[_ -> {c_, i_} /; MatchQ[c, I | -I]] :> i]
    ];
    j = With[{keys = Complement[v["Indices"], Keys[is]]}, AssociationThread[keys, Lookup[assoc, Key /@ keys, 0]]];
    Multivector[
        Association[I Values[#] . Lookup[assoc, Keys[#], 0] & /@ is, j],
        G
    ]
]


Options[MultivectorMatrix] = {"Basis" -> Automatic};

MultivectorMatrix[v_Multivector, opts: OptionsPattern[]] := Block[{
    w, p, q, n, X, M, mat
},
    w = DualComplexMultivector[v];
    {p, q} = w["ComplexSignature"];

    n = Floor[(p + q) / 2];

    M = MatrixInverse @ If[
        OptionValue["Basis"] === Automatic,
        nilpotentMatrix[n],

        multivectorBasisMatrix[OptionValue["Basis"]]
    ];
    X = MultivectorNumber /@ ConvertGeometricAlgebra[w, w["BalancedAlgebra"]]["ComplexCoordinates"];
    mat = MultivectorArray[Partition[M . X, 2 ^ n]];

    mat
]


Options[MultivectorBlock] = {}

MultivectorBlock[v_Multivector, opts: OptionsPattern[]] := Block[{
    w, G, n, p, q, X, F, B
},
    w = DualComplexMultivector[v];
    {p, q} = w["ComplexSignature"];

    n = Floor[(p + q) / 2];
    If[ n > 0,
        G = GeometricAlgebra @ MapThread[Max, {w["BalancedAlgebra"]["Signature"] - {1, 1, 0}, {0, 0, 0}}];
        X = MultivectorNumber[#, G["BalancedAlgebra"]] & /@ ConvertGeometricAlgebra[w, w["BalancedAlgebra"]]["ComplexCoordinates"];
        F = MatrixInverse @ nilpotentMatrix[n];
        B = nilpotentMatrix[n - 1];
        BlockMap[
            Multivector[AssociationThread[G[If[OddQ[p + q], "ReIndices", "Indices"]], (B . Flatten[#, 1]) . X], G]["Flatten"] &,
            Partition[F, 2 ^ n],
            {2 ^ (n - 1), 2 ^ (n - 1)}
        ],

        {{w}}
    ] // MultivectorArray
]

MultivectorBlock[v_Multivector, n_Integer /; n > 0, opts : OptionsPattern[MultivectorMatrix]] :=
    With[{
        blocks = MultivectorBlock[v, opts]
    },
        If[ n > 1,
            MultivectorArray @ Flatten[Map[MultivectorBlock[#, n - 1, opts]["Components"] &, blocks["Components"], {2}], {{1, 3}, {2, 4}}],
            blocks
        ]
    ]

MultivectorBlock[v_Multivector, 0, ___] := MultivectorArray[{{v}}]


Options[MatrixMultivector] = {"Basis" -> Automatic, Method -> "Matrix"};

MatrixMultivector::unknownMethod = "Method should be one of {\"Basis\", \"Matrix\"}";
MatrixMultivector::nonsq = "Not a square matrix";
MatrixMultivector::non2pow = "Matrix dimension `1` is not a power of 2";
MatrixMultivector::invalidBasis = "Specified basis is not a multivector of right dimensions";

MatrixMultivector[mat_MultivectorArray, opts: OptionsPattern[]] := Block[{
    dim, n, g, G, m, basis, M, X
},
    dim = Dimensions[mat];
    If[ Length[dim] != 2 || Not[Equal @@ dim],
        Message[MatrixMultivector::nonsq];
        Return[$Failed]
    ];
    n = Log2[First @ dim];
    If[ Not[IntegerQ[n]],
        Message[MatrixMultivector::non2pow, dim];
        Return[$Failed]
    ];

    g = mat["GeometricAlgebra"];
    If[ g["ComplexDimension"] > 1,
        m = Floor[g["ComplexDimension"] / 2];
        Return @ MatrixMultivector[
            MultivectorArray[
                Flatten[
                    Map[
                        MultivectorMatrix[#, Sequence @@ FilterRules[{opts}, Options[MultivectorMatrix]]]["Components"] &,
                        mat["Components"],
                        {mat["Rank"]}
                    ],
                    {{1, 3}, {2, 4}}
                ],
                {2 ^ (n + m), - 2 ^ (n + m)}
            ],
            opts
        ]
    ];

    Switch[
        OptionValue[Method],

        "Basis",

        If[
            OptionValue["Basis"] === Automatic,

            (* Construct nilpotent basis *)
            basis = nilpotentBasis[n],

            (* Explicit basis *)
            If[
                Not[MatchQ[OptionValue["Basis"], _MultivectorArray] && Dimensions[OptionValue["Basis"]] == Dimensions[mat]],

                Message[MatrixMultivector::invalidBasis];
                Return[$Failed],

                basis = OptionValue["Basis"][CanonicalMultivector]
            ]

        ];
        M = mat[MultivectorNumber]["Components"];
        Total[MapThread[#2[Map[Curry[Times][#1]]] &, {M, basis["Components"]}, 2], 2],

        "Matrix",
        G = GeometricAlgebra[{n, n}];
        X = Catenate @ mat[MultivectorNumber]["Components"];
        M = If[
            OptionValue["Basis"] === Automatic,

            nilpotentMatrix[n],

            If[
                Not[MatchQ[OptionValue["Basis"], _MultivectorArray] && Dimensions[OptionValue["Basis"]] == Dimensions[mat]],

                Message[MatrixMultivector::invalidBasis];
                Return[$Failed],

                multivectorBasisMatrix[OptionValue["Basis"]]

            ]
        ];
        Multivector[
            M . X,
            G
        ],

        _,
        Message[MatrixMultivector::unknownMethod];
        $Failed
    ]
]

MatrixMultivector[mat_MultivectorArray, g_GeometricAlgebra, opts : OptionsPattern[]] := Block[{cg = g["ComplexAlgebra"], bg = g["BalancedAlgebra"]},
    ConvertGeometricAlgebra[
        ComplexDualMultivector[
            ConvertGeometricAlgebra[MatrixMultivector[mat, opts][Map[NumberMultivector[#, bg] &]]["Flatten"], cg],
            g["DualDimension"]
        ],
        g
    ]
]

MatrixMultivector[mat_MultivectorArray, g_, opts : OptionsPattern[]] := MatrixMultivector[mat, GeometricAlgebra[g], opts]


MultivectorFunction[f_ /; MatchQ[f, _Function] || numericFunctionQ[f], mat_ /; SquareMatrixQ[mat] && MatrixQ[mat, MultivectorQ], opts: OptionsPattern[]] := Enclose @ Block[{
    re, im, g, d, a, b, result
},
    g = mat[[1, 1]]["GeometricAlgebra"];
    d = g["Dimension"];
    If[ d == 0,
        With[{duals = DualCoordinates[Map[#["Scalar"] &, mat, {2}]]},
            With[{n = Ceiling @ Log2[Max[Map[Length, duals, {2}]]]},
                result = applyDualFunction[ConfirmBy[MatrixFunction[f, #], MatrixQ] &, Transpose[Map[PadRight[#, 2 ^ n] &, duals, {2}], {2, 3, 1}], n]
            ]
        ]
        ,
        re = Map[#["Scalar"] &, mat, {2}];
        im = Map[#["Pseudoscalar"] &, mat, {2}];
        Switch[g["PseudoscalarSquare"],
            1,
            (* hyperbolic (split-complex) case *)
            With[{
                aDuals = DualCoordinates[re + im],
                bDuals = DualCoordinates[re - im]
            },
                With[{n = Ceiling @ Log2[Max[Map[Length, Join[aDuals, bDuals, 3], {2}]]]},
                    a = applyDualFunction[ConfirmBy[MatrixFunction[f, #], MatrixQ] &, Transpose[Map[PadRight[#, 2 ^ n] &, aDuals, {2}], {2, 3, 1}], n];
                    b = applyDualFunction[ConfirmBy[MatrixFunction[f, #], MatrixQ] &, Transpose[Map[PadRight[#, 2 ^ n] &, bDuals, {2}], {2, 3, 1}], n];
                ]
            ];
            result = MapThread[Function[{x, y}, Multivector[{x, y}, GeometricAlgebra[1, 0]], HoldAllComplete], {a + b, a - b} / 2, 2],

            -1,
            (* complex case *)
            With[{
                aDuals = DualCoordinates[re + I im],
                bDuals = DualCoordinates[re - I im]
            },
                With[{n = Ceiling @ Log2[Max[Map[Length, Join[aDuals, bDuals, 3], {2}]]]},
                    a = applyDualFunction[ConfirmBy[MatrixFunction[f, #], MatrixQ] &, Transpose[Map[PadRight[#, 2 ^ n] &, aDuals, {2}], {2, 3, 1}], n];
                    b = applyDualFunction[ConfirmBy[MatrixFunction[f, #], MatrixQ] &, Transpose[Map[PadRight[#, 2 ^ n] &, bDuals, {2}], {2, 3, 1}], n];
                ]
            ];
            result = MapThread[Function[{x, y}, Multivector[{x, - I y}, GeometricAlgebra[0, 1]], HoldAllComplete], {a + b, a - b} / 2, 2],
            
            _,
            Return[$Failed]
        ]
    ];
    MultivectorArray[result]
]

MultivectorFunction[f_ /; MatchQ[f, _Function] || numericFunctionQ[f], va_MultivectorArray ? MultivectorArrayQ, opts: OptionsPattern[]] :=
    MultivectorFunction[f, Normal[va], opts]

MultivectorFunction[f_ /; MatchQ[f, _Function] || numericFunctionQ[f], v_Multivector ? MultivectorQ, opts: OptionsPattern[]] := Enclose @ Block[{
    w, x, y
},
    w = DualComplexMultivector[v];
    x = Confirm @ MultivectorMatrix[w, FilterRules[{opts}, Options[MultivectorMatrix]]];

    y = Confirm @ MultivectorFunction[f, x, opts];

    ConvertGeometricAlgebra[
        ConvertGeometricAlgebra[MatrixMultivector[y, w["BalancedAlgebra"], FilterRules[{opts}, Options[MatrixMultivector]]], w["GeometricAlgebra"]],
        v["GeometricAlgebra"]
    ]
]


v_Multivector["Matrix"] := MultivectorMatrix[v]

MultivectorPower[v_Multivector, n_] := MultivectorFunction[# ^ n &, v]

MultivectorExp[v_Multivector, opts: OptionsPattern[]] := MultivectorFunction[Exp, v, opts]

MultivectorLog[v_Multivector, opts: OptionsPattern[]] := MultivectorFunction[Log, v, opts]

Multivector /: (f : Eigenvalues | Eigenvectors | Eigensystem)[v_Multivector, opts: OptionsPattern[]] := f[MultivectorMatrix[v, opts]["Numeric"]]


DualComplexMultivector[v_Multivector] := Block[{
    p, q, r, G
},
    {p, q, r} = v["Signature"];
    If[r == 0, Return[v]];
    G = GeometricAlgebra[p + r, q + r];
    Multivector[
        Association @ KeyValueMap[
            Function[{k, x}, If[AnyTrue[k, GreaterThan[p]], With[{l = Replace[k, i_ :> If[i > p, p - q - i, i], 1]}, <|k -> x, l -> x|> / 2], k -> x]],
            v["Association"]
        ],
        G
    ]
]


ComplexDualMultivector[v_Multivector, r_Integer : 1] := Block[{
    p, q, G
},
    If[r == 0, Return[v]];
    {p, q} = v["ComplexSignature"];
    G = GeometricAlgebra[p - r, q - r, r];
    Multivector[
        Merge[KeyValueMap[Replace[#1, i_ :> If[i < - q + r, p - q - i, i], 1] -> #2 &, v["Association"]], Total],
        G
    ]
]

(* Utility functions *)


nilpotentBasis[0] := MultivectorArray[{{1}}]

nilpotentBasis[n_Integer] := Block[{A, u, Bt, G},
    G = GeometricAlgebra[n, n + 1];
    A = Apply[LeftKroneckerProduct,
        Table[
            MultivectorArray[{Multivector[1, G], G["Nilpotent", i]}],
            {i, 1, n}
        ]
    ];
    u = Apply[GeometricProduct, Table[G["Idempotent", i], {i, 1, n}]];
    Bt = Apply[RightKroneckerProduct,
        Reverse @ Table[
            MultivectorArray[{Multivector[1, G], G["Nilpotent", -i]}, {-2}],
            {i, 1, n}
        ]
    ];
    GeometricProduct[A, u, Bt]
]


multivectorBasisMatrix[arr_MultivectorArray] := multivectorBasisMatrix[arr] = Block[{
    n, m, sa, s
},
    n = Log2[arr["Dimension"]] / 2;
    m = 2 ^ n;
    If[Not @ arr["DoubleSquareQ"], Return[$Failed]];
    sa = Array[s[##] &, {m, m}];


    Coefficient[#["Scalar"], Flatten @ sa] & /@
        MatrixMultivector[MultivectorArray[sa], Method -> "Basis", "Basis" -> arr[CanonicalMultivector]]["ComplexCoordinates"]
]


nilpotentMatrix[n_Integer] := nilpotentMatrix[n] = multivectorBasisMatrix[nilpotentBasis[n]]
