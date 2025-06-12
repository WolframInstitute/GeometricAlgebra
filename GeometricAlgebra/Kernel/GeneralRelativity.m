Package["Wolfram`GeometricAlgebra`GeneralRelativity`"]

PackageImport["Wolfram`GeometricAlgebra`"]

PackageExport[CoordinateFrames]
PackageExport[TetradFrames]
PackageExport[Vierbein]
PackageExport[InverseVierbein]
PackageExport[ToTetrad]
PackageExport[ToInverseTetrad]

PackageExport[PartialDerivatives]
PackageExport[CoordinateDerivative]
PackageExport[VectorDerivative]
PackageExport[CovariantDerivative]
PackageExport[SpinConnection]
PackageExport[SpinConnectionComponents]
PackageExport[ChristoffelSymbols]
PackageExport[RiemannMap]
PackageExport[RicciMap]
PackageExport[RicciScalar]
PackageExport[WeylMap]
PackageExport[KretschmannScalar]
PackageExport[EinsteinMap]



$DefaultVars = {\[FormalT], \[FormalX], \[FormalY], \[FormalZ]}


CanonicalVariableName[v_Symbol ? AtomQ] := With[{w = Unevaluated @@ ResourceFunction["UnformalizeSymbols"][v, "DeferQ" -> True]}, ToString[w]]

CanonicalVariableName[v_] := v

$DefaultNames = CanonicalVariableName /@ $DefaultVars


PartialDerivatives[vars : {__Symbol ? AtomQ} : $DefaultVars] := (v |-> D[#, v] &) /@ vars


Vierbein[g_ ? GeometricAlgebraQ] := g["VectorBasis"]

InverseVierbein[g_ ? GeometricAlgebraQ] := Inverse[Vierbein[g]]


ToTetrad[g_ ? GeometricAlgebraQ] := GeometricAlgebra[g["Signature"]]

ToTetrad[v_ ? MultivectorQ] := ConvertGeometricAlgebra[v, ToTetrad[GeometricAlgebra[v]]]

ToInverseTetrad[g_ ? GeometricAlgebraQ] := GeometricAlgebra[g["Signature"], "VectorBasis" -> g["SignatureMetric"]]

ToInverseTetrad[v_ ? MultivectorQ] := ConvertGeometricAlgebra[v, ToInverseTetrad[GeometricAlgebra[v]]]


TetradFrames[vectorNames : {_, _, _, _} : $DefaultNames, name_ : "\[Gamma]", indexName_ : "m"] := With[{
    repl = Append["e" -> name] @ Thread[{1, UnderBar[3], UnderBar[2], UnderBar[1]} -> CanonicalVariableName /@ vectorNames]
},
    {
        GeometricAlgebra[1, 3, 
            "Format" -> Subscript[name, indexName],
            "FormatIndex" -> Function[
                $DefaultMultivectorFormatFunction[#] /. repl
            ]
        ],
        GeometricAlgebra[1, 3, 
            "Format" -> Superscript[name, indexName],
            "FormatIndex" -> Function[
                $DefaultMultivectorFormatFunction[#] /. Append[Subscript -> Superscript] @ repl
            ],
            "VectorBasis" -> DiagonalMatrix[{1, -1, -1, -1}]
        ]
    }
]


CoordinateFrames[e_ /; SquareMatrixQ[e] && Dimensions[e] == {4, 4}, vectorNames : {_, _, _, _} : $DefaultNames, name_ : "g", indexName_ : "\[Mu]"] := With[{
    repl = Append["e" -> name] @ Thread[{1, UnderBar[3], UnderBar[2], UnderBar[1]} -> CanonicalVariableName /@ vectorNames],
    eta = DiagonalMatrix[{1, -1, -1, -1}]
},
    {
        GeometricAlgebra[1, 3, 
            "Format" -> Subscript[name, indexName],
            "FormatIndex" -> Function[
                $DefaultMultivectorFormatFunction[#] /. repl
            ],
            "VectorBasis" -> e
        ],
        GeometricAlgebra[1, 3, 
            "Format" -> Superscript[name, indexName],
            "FormatIndex" -> Function[
                $DefaultMultivectorFormatFunction[#] /. Append[Subscript -> Superscript] @ repl
            ],
            "VectorBasis" -> eta . Inverse[e]
        ]
    }
]


CoordinateDerivative[g_ ? GeometricAlgebraQ, vars : {__Symbol ? AtomQ} : $DefaultVars] /; g["Dimension"] == Length[vars] := With[{
    pd = PartialDerivatives[vars]
},
    Multivector[pd . g["SignatureMetric"] . g["Basis", 1], Right][Identity]
]

CoordinateDerivative[vars : {__Symbol ? AtomQ} : $DefaultVars] := CoordinateDerivative[TetradFrames[CanonicalVariableName /@ vars][[2]], vars]


SpinConnection[g_ ? GeometricAlgebraQ, vars : {__Symbol ? AtomQ} : $DefaultVars] := With[{
    cd = CoordinateDerivative[g, vars],
    pd = PartialDerivatives[vars],
    e = Vierbein[g],
    gmu = g["SignatureMetric"] . g["Basis", 1]
},
    ConvertGeometricAlgebra[
        1 / 2 Total @ MapThread[
            Wedge[#1, Flatten[GeometricProduct[cd, Multivector[#2, g]]]] &,
            {gmu, #}
        ],
        g
    ] & /@ g["Metric"] + (Inner[Wedge, g["Basis", 1], ToInverseTetrad[g]["Basis", 1] . #[e]] & /@ pd)
]

SpinConnectionComponents[omega : {Repeated[_ ? MultivectorQ, {4}]}] := With[{eta = omega[[1]]["SignatureMetric"]},
     eta . # & /@ Transpose[
        ArrayReshape[Comap[ToInverseTetrad /@ omega, Tuples[{1, -3, -2, -1}, 2]], {4, 4, 4}],
        {3, 2, 1}
    ]
]

ChristoffelSymbols[g_ ? GeometricAlgebraQ, vars : {__Symbol ? AtomQ} : $DefaultVars] := With[{
    omega = SpinConnectionComponents[SpinConnection[g, vars]],
    pd = PartialDerivatives[vars],
    e = Vierbein[g],
    einv = InverseVierbein[g]
},
    Transpose[einv] . Transpose[#[e] & /@ pd, {3, 1, 2}] + einv . Transpose[e . omega]
]


VectorDerivative[g_ ? GeometricAlgebraQ, vars_ : $DefaultVars] /; g["Dimension"] == Length[vars] := With[{
    cd = CoordinateDerivative[g, vars],
    omega = SpinConnection[g, vars]
},
    Multivector[Grade[(w |-> 1 / 2 Commutator[w, #] &) /@ omega, 1, g], Right]
]


RiemannMap[g_ ? GeometricAlgebraQ, vars_ : $DefaultVars] := With[{
    omega = ToTetrad /@ SpinConnection[g, vars],
    pd = PartialDerivatives[vars],
    e = InverseVierbein[g]
},
    Map[ConvertGeometricAlgebra[#, g] &, Transpose[e] . (Outer[#2[#1] &, pd, omega] - Outer[#1[#2] &, omega, pd] + 1 / 2 Outer[Commutator, omega, omega]) . e, {2}]
]

RicciMap[riemann_ ? SquareMatrixQ] := With[{g = GeometricAlgebra[riemann[[1, 1]]]},
    ConvertGeometricAlgebra[#, g] & /@ Inner[Dot, ToInverseTetrad[g]["Basis", 1], riemann]
]

RicciMap[g_ ? GeometricAlgebraQ, vars_ : $DefaultVars] := RicciMap[RiemannMap[g, vars]]

RicciScalar[ricci_ ? VectorQ] := Inner[Dot, ToInverseTetrad[GeometricAlgebra[ricci[[1]]]]["Basis", 1], ricci]

RicciScalar[g_ ? GeometricAlgebraQ, vars_ : $DefaultVars] := RicciScalar[RicciMap[g, vars]]

WeylMap[g_ ? GeometricAlgebraQ, vars_ : $DefaultVars] :=  With[{gamma = ToTetrad[g]["Basis", 1], riemann = RiemannMap[g, vars]}, {ricci = RicciMap[riemann]}, {r = RicciScalar[ricci]},
    riemann - 1 / 2 (Outer[Wedge, ricci, gamma] + Outer[Wedge, gamma, ricci]) + 1 / 6 GeometricProduct[r, Outer[Wedge, gamma, gamma]]
]

EinsteinMap[ricci_ ? VectorQ] := With[{g = GeometricAlgebra[ricci[[1]]]}, {gamma = ToTetrad[g]["Basis", 1], r = RicciScalar[ricci]},
    MapThread[ConvertGeometricAlgebra[#2 - 1 / 2 GeometricProduct[#1, r], g] &, {gamma, ricci}]
]

EinsteinMap[g_ ? GeometricAlgebraQ, vars_ : $DefaultVars] := EinsteinMap[RicciMap[g, vars]]

KretschmannScalar[g_ ? GeometricAlgebraQ, vars_ : $DefaultVars] := With[{r = Map[ToInverseTetrad, RiemannMap[g, vars], {2}], eta = g["SignatureMetric"]},
    ConvertGeometricAlgebra[Tr @ Tr[r . eta . r . eta], g]
]

