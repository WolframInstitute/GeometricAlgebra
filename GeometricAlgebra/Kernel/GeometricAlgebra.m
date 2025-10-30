Package["Wolfram`GeometricAlgebra`"]


PackageExport["GeometricAlgebra"]
PackageExport["GeometricAlgebraQ"]

PackageScope["$GeometricAlgebraProperties"]
PackageScope["lowerGeometricAlgebra"]
PackageScope["higherGeometricAlgebra"]


GeometricAlgebra::usage = "GeometricAlgebra[p, q] gives an underlying algebra object for use with Multivector";


Options[GeometricAlgebra] = {"Signature" -> {3, 0, 0}, "VectorBasis" -> Automatic, "Format" -> Automatic, "FormatIndex" -> Automatic, "Ordering" -> Automatic}


$GeometricAlgebraProperties = {
    "Format",
    "FormatIndex",

    "Signature",
    "ComplexSignature",
    "DualSignature",

    "Dimension",
    "DualDimension",
    "ComplexDimension",
    "NegativeDimension",
    "NonNegativeDimension",

    "Order", "Size",
    "ComplexOrder",
    "DualOrder",

    "Ordering",

    "VectorBasis",
    "SignatureMetric",
    "Metric",
    "MetricSignature",
    "Indices",
    "DualIndices",
    "OrderedIndices",
    "ReIndices",
    "ImIndexSigns",

    "Basis",
    "PseudoBasis",
    "OrderedBasis",

    "MultiplicationMatrix",
    "MultiplicationTable",
    "ExomorphismMatrix",
    "AntiExomorphismMatrix",

    "PseudoscalarIndex",
    "PseudoscalarSquare",

    "BalancedAlgebra",
    "ComplexAlgebra",
    "NumberAlgebra",

    "Zero",
    "Identity",
    "Origin",
    "Infinity"
};


geometricAlgebraQ[HoldPattern[GeometricAlgebra[data_Association ? AssociationQ]]] :=
    MatchQ[data, KeyValuePattern["Signature" -> {Repeated[_Integer ? NonNegative, {3}]}]];

geometricAlgebraQ[___] := False


GeometricAlgebraQ[g_GeometricAlgebra] := System`Private`HoldValidQ[g] || geometricAlgebraQ[Unevaluated[g]]

GeometricAlgebraQ[___] := False


GeometricAlgebra[p_Integer, q_Integer: 0, r_Integer: 0, opts: OptionsPattern[]] :=
    GeometricAlgebra["Signature" -> {p, q, r}, opts]

GeometricAlgebra[{p_Integer, q___Integer}, opts: OptionsPattern[]] := GeometricAlgebra[p, q, opts]

GeometricAlgebra[g_GeometricAlgebra, opts: OptionsPattern[]] :=
    GeometricAlgebra[Merge[Join[FilterRules[{opts}, Options[GeometricAlgebra]], Options[g]], First]]

GeometricAlgebra[] := OptionValue[Multivector, "GeometricAlgebra"] (* current default GeometricAlgebra *)

GeometricAlgebra[opts : OptionsPattern[]] := GeometricAlgebra[Association[opts]]

GeometricAlgebra /: HoldPattern[Options[GeometricAlgebra[data_] ? GeometricAlgebraQ]] := Normal[data]

GeometricAlgebra /: HoldPattern[Options[GeometricAlgebra[data_] ? GeometricAlgebraQ, filter_]] := FilterRules[Normal[data], filter]

g_GeometricAlgebra[opt_String] /; KeyExistsQ[Options[GeometricAlgebra], opt] := With[{value = OptionValue[{Options[g], Options[GeometricAlgebra]}, opt]},
    Switch[opt,
        "VectorBasis",
        Replace[value, Automatic :> If[g["Dimension"] == 0, {{}}, IdentityMatrix[g["Dimension"]]]],
        _,
        value
    ]
]

g_GeometricAlgebra["Metric"] := Replace[g["VectorBasis"], {
    Automatic :> If[g["Dimension"] == 0, {{}}, DiagonalMatrix[g["MetricSignature"]]],
    b_ ? SquareMatrixQ :> Transpose[b] . DiagonalMatrix[g["MetricSignature"]] . b,
    b_ ? VectorQ :> g["MetricSignature"] * b ^ 2
}]

g_GeometricAlgebra["ComplexSignature"] := g["Signature"][[;; 2]]

g_GeometricAlgebra["DualSignature" | "DualDimension"] := g["Signature"][[3]]

g_GeometricAlgebra["Dimension"] := Total @ g["Signature"]

g_GeometricAlgebra["NegativeDimension"] := g["Signature"][[2]]

g_GeometricAlgebra["NonNegativeDimension"] := Total @ g["Signature"][[{1, 3}]]

g_GeometricAlgebra["ComplexDimension"] := Total @ g["ComplexSignature"]

g_GeometricAlgebra["Order" | "Size"] := 2 ^ g["Dimension"]

g_GeometricAlgebra["ComplexOrder"] := 2 ^ g["ComplexDimension"]

g_GeometricAlgebra["DualOrder"] := 2 ^ g["DualDimension"]

g_GeometricAlgebra["MetricSignature"] :=
    Module[{p, q, r},
        {p, q, r} = g["Signature"];
        Join[ConstantArray[1, p], ConstantArray[0, r], ConstantArray[-1, q]]
    ]

g_GeometricAlgebra["SignatureMetric"] := DiagonalMatrix[g["MetricSignature"]]

g_GeometricAlgebra["Indices"] := g["Indices"] = Block[{
    p, q, r
},
    {p, q, r} = g["Signature"];
    Subsets[Join[Range[p], p + Range[r], Range[- q, -1]]]
]

g_GeometricAlgebra["OrderedIndices"] := g["OrderedIndices"] =
    With[{s = g["Signature"]}, Replace[g["Ordering"], {Automatic :> g["Indices"], xs : {{___Integer} ...} :> Map[normalIndex[#, s] &, xs, {2}]}]]

g_GeometricAlgebra["DualIndices"] := With[{i = Last @ g["Indices"]},
     Map[DeleteElements[i, #] &, g["Indices"]]
]

g_GeometricAlgebra["PseudoscalarIndex"] := g["PseudoscalarIndex"] = With[{i = Last[g["Indices"]]},
    If[g["Ordering"] === Automatic, i, SelectFirst[g["OrderedIndices"], Sort[#] == i &, i]]
]

g_GeometricAlgebra["PseudoscalarSquare"] := Block[{p, q, r},
    {p, q, r} = g["Signature"];
    If[r == 0, (- 1) ^ ((p - q) * (p - q - 1) / 2), 0]
]


g_GeometricAlgebra["BalancedAlgebra"] := With[{n = Floor[g["ComplexDimension"] / 2], r = g["DualDimension"]},
    If[ OddQ[g["ComplexDimension"]],
        If[ g["PseudoscalarSquare"] == 1,
            GeometricAlgebra[n + 1 + r, n + r],
            GeometricAlgebra[n + r, n + 1 + r]
        ],
        GeometricAlgebra[n + r, n + r]
    ]
]

g_GeometricAlgebra["ComplexAlgebra"] := Block[{p, q, r},
    {p, q, r} = g["Signature"];
    If[ r > 0,
        GeometricAlgebra[p + r, q + r],
        g
    ]
]

g_GeometricAlgebra["NumberAlgebra"] := If[g["PseudoscalarSquare"] == 1, GeometricAlgebra[1], GeometricAlgebra[0, 1]]


middleIndex[g_GeometricAlgebra] := Module[{p, q},
    {p, q} = g["ComplexSignature"];
    Join[Range[p], Range[-q, -1]][[Ceiling[(p + q) / 2]]]
]

g_GeometricAlgebra["ReIndices"] := Cases[g["Indices"], _List ? (FreeQ[#, middleIndex[g]] &)]

g_GeometricAlgebra["ImIndexSigns"] := With[{i = Last @ g["Indices"]}, Rule @@ KeyMap[Reverse] @ multiplyIndices[i, #, g["Metric"]] & /@ g["ReIndices"]]


GeometricAlgebra /: Equal[gs__GeometricAlgebra]:= Equal @@ Through[{gs}["Signature"]] && Equal @@ Through[{gs}["VectorBasis"]] 


g_GeometricAlgebra /; System`Private`HoldNotValidQ[g] && geometricAlgebraQ[Unevaluated[g]] := System`Private`SetNoEntry[System`Private`HoldSetValid[g]]


(* Boxes *)


GeometricAlgebra /: MakeBoxes[g_GeometricAlgebra /; GeometricAlgebraQ[Unevaluated[g]], form___] := With[{
    box = ToBoxes[Replace[g["Format"], Automatic :> Subscript["\[DoubleStruckCapitalG]", Row @ Riffle[ToString /@ Replace[MapAt[Replace[0 -> Nothing], g["Signature"], {3}], {p_, 0} :> {p}], ","]]], form],
    tooltip = RowBox[{"Geometric Algebra", ToBoxes[g["Signature"], form]}]
},
    InterpretationBox[box, g, Tooltip -> tooltip]
]


(* Utility functions *)

lowerGeometricAlgebra[g_GeometricAlgebra] := Module[{
    p, q, r
},
    {p, q, r} = g["Signature"];
    GeometricAlgebra @ If[p >= q, {Max[p - 1, 0], q, r}, {p, q - 1, r}]
]

higherGeometricAlgebra[g_GeometricAlgebra] := Module[{
    p, q, r
},
    {p, q, r} = g["Signature"];
    GeometricAlgebra @ If[p > q, {p, q + 1, r}, {p + 1, q, r}]
]
