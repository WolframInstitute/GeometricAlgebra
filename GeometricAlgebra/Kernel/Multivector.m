Package["Wolfram`GeometricAlgebra`"]


PackageExport["Multivector"]
Multivector::usage = "Multivector[coords, ga] gives a multivector in GeometricAlgebra ga";

PackageExport["MultivectorQ"]

PackageExport["NumberMultivector"]
NumberMultivector::usage = "NumberMultivector[x, ga] gives a multivector corresponding to a complex number x in geometric algebra ga";

PackageExport["MultivectorNumber"]
MultivectorNumber::usage = "MultivectorNumber[v] gives a complex number based on scalar and pseudoscalar parts of multivector";

PackageExport["BalancedMultivector"]

PackageExport["GeometricProduct"]
GeometricProduct::usage = "GeometricProduct[vs__] computes geometric product of multivectors";

PackageExport["AntiGeometricProduct"]
AntiGeometricProduct::usage = "AntiGeometricProduct[v, w] gives an anti geometric product of multivectors v and w";

PackageExport["Grade"]
Grade::usage = "Grade[v, n] gives a nth grade of a Multivector v or converts a list to a multivector";

PackageExport["AntiGrade"]
AntiGrade::usage = "AntiGrade[v, n] gives a nth anti grade of a Multivector v or converts a list to a multivector";

PackageExport["GradeList"]
GradeList::usage = "GradeList[v] gives a list of all grades of multivector";

PackageExport["WedgeProduct"]
WedgeProduct::usage = "WedgeProduct[v, w] gives a wedge product of multivectors v and w";

PackageExport["AntiWedgeProduct"]
AntiWedgeProduct::usage = "AntiWedgeProduct[v, w] gives an anti wedge product of multivectors v and w";

PackageExport["DotProduct"]
DotProduct::usage = "DotProduct[v, w] gives a dot product of multivectors v and w";

PackageExport["AntiDotProduct"]
AntiDotProduct::usage = "AntiDotProduct[v, w] gives an anti dot product of multivectors v and w";

PackageExport["LeftContraction"]
LeftContraction::usage = "LeftContraction[v, w] gives a left contraction of multivectors v and w";

PackageExport["RightContraction"]
RightContraction::usage = "RightContraction[v, w] gives a right contraction of multivectors v and w";

PackageExport["ScalarProduct"]
ScalarProduct::usage = "ScalarProduct[v, w] gives a scalar product of multivectors v and w";

PackageExport["CrossProduct"]
CrossProduct::usage = "CrossProduct[v, w] gives a cross product of multivectors v and w";

PackageExport["InnerProduct"]
InnerProduct::usage = "InnerProduct[v, w] gives an inner product of multivectors v and w";

PackageExport["AntiInnerProduct"]
AntiInnerProduct::usage = "AntiInnerProduct[v, w] gives an anti inner product of multivectors v and w";

PackageExport["RightInteriorProduct"]
RightInteriorProduct::usage = "RightInteriorProduct[v, w] gives a right interior product of multivectors v and w";

PackageExport["LeftInteriorProduct"]
LeftInteriorProduct::usage = "LeftInteriorProduct[v, w] gives a left interior product of multivectors v and w";

PackageExport["RightInteriorAntiProduct"]
RightInteriorAntiProduct::usage = "RightInteriorAntiProduct[v, w] gives a right interior anti product of multivectors v and w";

PackageExport["LeftInteriorAntiProduct"]
LeftInteriorAntiProduct::usage = "LeftInteriorAntiProduct[v, w] gives a left interior anti product of multivectors v and w";

PackageExport["BulkExpansion"]
BulkExpansion::usage = "BulkExpansion[v] gives a bulk expansion of multivector v";

PackageExport["WeightExpansion"]
WeightExpansion::usage = "WeightExpansion[v] gives a weight expansion of multivector v";

PackageExport["BulkContraction"]
BulkContraction::usage = "BulkContraction[v, w] gives a bulk contraction of multivectors v and w";

PackageExport["WeightContraction"]
WeightContraction::usage = "WeightContraction[v, w] gives a weight contraction of multivectors v and w";

PackageExport["LeftComplement"]
LeftComplement::usage = "LeftComplement[v] gives a left complement of multivector v";

PackageExport["RightComplement"]
RightComplement::usage = "RightComplement[v] gives a right complement of multivector v";

PackageExport["LeftDual"]
LeftDual::usage = "LeftDual[v] gives a left dual of multivector v";

PackageExport["RightDual"]
RightDual::usage = "RightDual[v] gives a right dual of multivector v";

PackageExport["Bulk"]
Bulk::usage = "Bulk[v] gives a bulk of multivector v";

PackageExport["Weight"]
Weight::usage = "Weight[v] gives a weight of multivector v";

PackageExport["RightBulkDual"]
PackageExport["BulkDual"]
RightBulkDual::usage = "RightBulkDual[v] gives a right bulk dual of multivector v";

PackageExport["RightWeightDual"]
PackageExport["WeightDual"]
RightWeightDual::usage = "RightWeightDual[v] gives a right weight dual of multivector v";

PackageExport["LeftBulkDual"]
LeftBulkDual::usage = "LeftBulkDual[v] gives a left bulk dual of multivector v";

PackageExport["LeftWeightDual"]
LeftWeightDual::usage = "LeftWeightDual[v] gives a left weight dual of multivector v";

PackageExport["FlatPart"]
FlatPart::usage = "FlatPart[v] gives a flat part of multivector v";

PackageExport["RoundPart"]
RoundPart::usage = "RoundPart[v] gives a round part of multivector v";

PackageExport["RoundBulk"]
RoundBulk::usage = "RoundBulk[v] gives a round bulk of multivector v";

PackageExport["FlatBulk"]
FlatBulk::usage = "FlatBulk[v] gives a flat bulk of multivector v";

PackageExport["RoundWeight"]
RoundWeight::usage = "RoundWeight[v] gives a round weight of multivector v";

PackageExport["FlatWeight"]
FlatWeight::usage = "FlatWeight[v] gives a flat weight of multivector v";

PackageExport["Carrier"]
Carrier::usage = "Carrier[v] gives a carrier of multivector v";

PackageExport["Cocarrier"]
Cocarrier::usage = "Cocarrier[v] gives a cocarrier of multivector v";

PackageExport["Container"]
Container::usage = "Container[v] gives a container of multivector v";

PackageExport["Partner"]
Partner::usage = "Partner[v] gives a partner of multivector v";

PackageExport["BulkNorm"]
BulkNorm::usage = "BulkNorm[v] gives a bulk norm of multivector v";

PackageExport["WeightNorm"]
WeightNorm::usage = "WeightNorm[v] gives a weight norm of multivector v";

PackageExport["GeometricNorm"]
GeometricNorm::usage = "GeometricNorm[v] gives a geometric norm of multivector v";

PackageExport["WeightUnitize"]
WeightUnitize::usage = "WeightUnitize[v] gives a multivector v unitized by its weight";

PackageExport["MultivectorCosAngle"]
MultivectorCosAngle::usage = "MultivectorCosAngle[v, w] gives a cosine of angle between multivectors v and w";

PackageExport["Involute"]
Involute::usage = "Involute[v] gives a multivector with its odd grades multiplied by -1";

PackageExport["Rejection"]
Rejection::usage = "Rejection[v, w] gives a rejection of multivector v on w";

PackageExport["OrthoProjection"]
OrthoProjection::usage = "OrthoProjection[v, w] gives an orthogonal projection of multivector v on w";

PackageExport["CentralProjection"]
CentralProjection::usage = "CentralProjection[v, w] gives a central projection of multivector v on w";

PackageExport["CentralAntiprojection"]
CentralAntiprojection::usage = "CentralAntiprojection[v, w] gives a central antiprojection of multivector v on w";

PackageExport["OrthoAntiprojection"]
OrthoAntiprojection::usage = "OrthoAntiprojection[v, w] gives an orthogonal antiprojection of multivector v on w";

PackageExport["Sandwich"]
Sandwich::usage = "Sandwich[v, w] gives a sandwich product of multivectors v and w";

PackageExport["AntiSandwich"]
AntiSandwich::usage = "AntiSandwich[v, w] gives an anti sandwich product of multivectors v and w";

PackageExport["AntiCommutator"]
AntiCommutator::usage = "AntiCommutator[v, w] gives an anti commutator of multivectors v ** w + w ** v";

PackageExport["AntiReverse"]
AntiReverse::usage = "AntiReverse[v] gives a multivector with its even grades multiplied by -1";

PackageExport["Attitude"]
Attitude::usage = "Attitude[v] gives an attitude of multivector v";

PackageExport["Support"]
Support::usage = "Support[v] gives a support of multivector v";

PackageExport["AntiSupport"]
AntiSupport::usage = "AntiSupport[v] gives an anti support of multivector v";

PackageExport["$DefaultMultivectorFormatFunction"]
$DefaultMultivectorFormatFunction::usage = "$DefaultMultivectorFormatFunction is a default function for formatting multivectors";

PackageExport["RandomMultivector"]
RandomMultivector::usage = "RandomMultivector[g] gives a random multivector in geometric algebra g";


PackageScope["zeroMultivector"]
PackageScope["identityMultivector"]
PackageScope["geometricIndexFormat"]
PackageScope["multiplyIndices"]
PackageScope["orderAndContract"]

PackageScope["switchDualSide"]


Options[Multivector] = {
    "GeometricAlgebra" -> GeometricAlgebra[3],
    "Orientation" -> Left
}


multivectorQ[HoldPattern[Multivector[coords_ /; MatchQ[coords, _SparseArray ? SparseArrayQ] || VectorQ[Unevaluated[coords]], g_ ? GeometricAlgebraQ, orientation : Left | Right : Left]]] := Length[coords] == g["Order"]

multivectorQ[___] := False


MultivectorQ[v_Multivector] := System`Private`HoldValidQ[v] || multivectorQ[Unevaluated[v]]

MultivectorQ[___] := False


$MultivectorProperties = {
    "GeometricAlgebra",
    "Coordinates",

    "Coordinate",
    "Association",
    "Span",
    "Grade",
    "Flatten",
    "Scalar",
    "Pseudoscalar",
    "Real",
    "ComplexCoordinates",

    "Reverse",
    "Involute",
    "Conjugate",
    "LeftComplement",
    "RightComplement",
    "DoubleComplement",
    "Squared",
    "Norm",
    "Normalized",

    "Inverse",

    "LeftDual",
    "RightDual",
    "Tr",
    "Det"
}


Multivector::truncCoord = "Coordinates are incompatible with `1`. Number of coordinates should be less than `2`. Truncating excessive coordinates.";


Multivector[coords_ ? VectorQ, g_ ? GeometricAlgebraQ, opts___] := With[{len = Length[coords], n = g["Order"]}, (
    If[len > n, Message[Multivector::truncCoord, g, n]];
    Multivector[SparseArray[coords, n], g, opts]
) /; len != n
]


Multivector[assoc_Association, g_ ? GeometricAlgebraQ, opts___] :=
    Multivector[Lookup[KeyValueMap[{index, x} |-> #1 -> x * #2 & @@ orderAndContract[normalIndex[index, g["Signature"]], g["Metric"]], assoc], g["Indices"], 0], g, opts]

Multivector[x_ ? NumericQ, g_ ? GeometricAlgebraQ, opts___] := NumberMultivector[x, g, opts]

Multivector[x : Except[_ ? VectorQ | _Multivector], g_ ? GeometricAlgebraQ, opts___] := Multivector[{x}, g, opts]

Multivector[x_, opts : OptionsPattern[]] := Multivector[x, OptionValue["GeometricAlgebra"]]

Multivector[x_, args : Except[_GeometricAlgebra | Left | Right] .., orientation : Left | Right : Left] := Multivector[x, GeometricAlgebra[args], orientation]

Multivector[x, p_Integer, q_Integer: 0, r_Integer: 0, opts___] := Multivector[x, GeometricAlgebra[p, q, r], opts]

Multivector[x_, {p_Integer, q_Integer: 0, r_Integer: 0}, opts___] := Multivector[x, p, q, r, opts]

Multivector[] := Multivector[{}]


NumberMultivector[x_, g_GeometricAlgebra, opts___] :=
    Multivector[SparseArray[{1 -> Re[x], -1 -> If[g["PseudoscalarSquare"] == 1, I, 1] Im[x]}, g["ComplexOrder"]], g, opts]

NumberMultivector[v_Multivector, g_GeometricAlgebra, opts___] :=
    Multivector[SparseArray[{1 -> v["Scalar"], -1 -> If[v["PseudoscalarSquare"] != g["PseudoscalarSquare"], I, 1] v["Pseudoscalar"]}, g["ComplexOrder"]], g, opts]

NumberMultivector[x_, args__, position : Left | Right : Left] := NumberMultivector[x, GeometricAlgebra[args], position]

NumberMultivector[x_] := NumberMultivector[x, GeometricAlgebra[0, 1]]


MultivectorNumber[v_Multivector, g_GeometricAlgebra] :=
    Multivector[SparseArray[{1 -> v["Scalar"], -1 -> v["Pseudoscalar"]}, g["ComplexOrder"]], g]

MultivectorNumber[v_Multivector] := MultivectorNumber[v, If[v["PseudoscalarSquare"] == 1, {1, 0}, {0, 1}]]

MultivectorNumber[x_, args__] := MultivectorNumber[x, GeometricAlgebra[args]]

MultivectorNumber[x_, ___] := x


BalancedMultivector[v_Multivector] := BalancedMultivector[v, GeometricAlgebra[v]]

BalancedMultivector[v_Multivector, g_GeometricAlgebra] := ConvertGeometricAlgebra[MultivectorNumber[v, g["BalancedAlgebra"]], g]


v_Multivector[key___Integer] := #2 Lookup[v["Association"], Key[#1], 0] & @@ orderIndexWithSign[normalIndex[DeleteCases[{key}, 0], v["Signature"]], v["Dimension"]]

v_Multivector[key : {___Integer}] := v /@ key

v_Multivector[keys : {{___Integer} ..}] := v @@@ keys



(HoldPattern[Multivector[coords_, _, ___]] ? MultivectorQ)["Coordinates"] := coords

Multivector /: Normal[v_Multivector] := Normal @ v["Coordinates"]


(HoldPattern[Multivector[_, g_, ___]] ? MultivectorQ)["GeometricAlgebra"] := g

GeometricAlgebra[v_Multivector] := v["GeometricAlgebra"]

(HoldPattern[Multivector[_, _, orientation : Left | Right : Left, ___]] ? MultivectorQ)["Orientation"] := orientation

(v_Multivector ? MultivectorQ)[prop_String /; MemberQ[$GeometricAlgebraProperties, prop], args___] := GeometricAlgebra[v][prop, args]


v_Multivector[f_] := mapCoordinates[f, v]


_Multivector["Properties"] := $MultivectorProperties

v_Multivector["Coordinates", n_Integer] := v["Coordinates"][[indexSpan[v, n]]]

v_Multivector["Coordinates", {ns__Integer}] := Join @@ (v["Coordinates", #] & /@ {ns})


v_Multivector["Coordinate", n_Integer] := v["Coordinates"][[n]]

v_Multivector["Coordinate", {ns__Integer}] := v["Coordinates"][[{ns}]]

Multivector /: Part[v_Multivector, keys___] := v["Coordinate", keys]


v_Multivector["CoordinateDimension"] := Max[DualDimension /@ v["Coordinates"]]


v_Multivector["Association"] := Association @ Map[Apply[Function[{x, y}, v["Indices"][[First[x]]] -> y, HoldAllComplete]], Most @ ArrayRules[v["Coordinates"]]]


v_Multivector["Span"] := MapThread[GeometricProduct, {v["Coordinates"], v["Basis"]}]

v_Multivector["Span", n_Integer] := MapThread[GeometricProduct, {v["Coordinates"][[indexSpan[v, n]]], v["Basis", n]}]

v_Multivector["Span", {ns__Integer}] := Catenate[v["Span", #] & /@ {ns}]


v_Multivector["Flatten", n_Integer : 1] :=
    Nest[If[v["Orientation"] === Left, Inner[GeometricProduct, #["Coordinates"], #["Basis"]] &, Inner[GeometricProduct, #["Basis"], #["Coordinates"]] &], v, n]

Multivector /: Flatten[v_Multivector, n_Integer : 1] := v["Flatten", n]

v_Multivector["Real"] := v[Re] + GeometricProduct[GeometricAlgebra[v]["Pseudoscalar"], v[Im]]


v_Multivector["Numeric"] := If[v["ComplexDimension"] > 0 && v["PseudoscalarSquare"] == 1,
    v["Scalar"] IdentityMatrix[2] +  v["Pseudoscalar"] Reverse @ IdentityMatrix[2],
    v["Scalar"] +  I v["Pseudoscalar"]
]


v_Multivector["ComplexCoordinates"] := Block[{
    g, re, im
},
    g = GeometricAlgebra[v];

    If[ OddQ[g["Dimension"]],
        re = Lookup[v["Association"], g["ReIndices"], 0];
        im = Lookup[GeometricProduct[v, g["Pseudoscalar"]]["Association"], g["ReIndices"], 0];

        re + GeometricProduct[g["PseudoscalarSquare"] im, g["Pseudoscalar"]]
        ,
        (* Even dimension *)
        v["Coordinates"]
    ]
]


v_Multivector /; System`Private`HoldNotValidQ[v] && multivectorQ[Unevaluated[v]] := System`Private`SetNoEntry[System`Private`HoldSetValid[v]]


(* Coersion *)

Multivector[v_Multivector] := v

Multivector[v_Multivector, g_GeometricAlgebra] /; GeometricAlgebra[v] === g := v

Multivector[v_Multivector, g_GeometricAlgebra] := Multivector[v["Association"], g]

Multivector[v_Multivector, orientation : Left | Right] := Multivector[v["Association"], v["GeometricAlgebra"], orientation]


(* Addition *)

zeroMultivector[g_GeometricAlgebra] := Multivector[{}, g]

zeroMultivector[v_Multivector] := zeroMultivector[GeometricAlgebra[v]]


Multivector /: Plus[vs__Multivector] /; Length[{vs}] > 1 := Block[{
    g = largestGeometricAlgebra[vs],
    ws
},
    ws = ConvertGeometricAlgebra[#, g] & /@ {vs};
    Multivector[
        Total[#["Coordinates"] & /@ ws],
        g,
        First[{vs}]["Orientation"]
    ][Identity]
]

Multivector /: Plus[x : Except[_Multivector], v_Multivector]:= x * identityMultivector[v] + v


g_GeometricAlgebra["Zero"] := zeroMultivector[g]


(* Scalar multiplication *)

identityMultivector[g_GeometricAlgebra] := Multivector[{1}, g]

identityMultivector[v_Multivector] := identityMultivector[GeometricAlgebra[v]]


Multivector /: Times[x : Except[_Multivector], v_Multivector] := mapCoordinates[x * # &, v]


v_Multivector["Scalar"] := v["Coordinate", 1]


v_Multivector["Pseudoscalar"] := If[v["Dimension"] > 0, v @@ v["PseudoscalarIndex"], 0]


g_GeometricAlgebra["Identity"] := identityMultivector[g]


(* Geometric Product *)

g_GeometricAlgebra["BasisMatrix"] := g["BasisMatrix"] = ExteriorMatrix[g["VectorBasis"]]

g_GeometricAlgebra["InverseBasisMatrix"] := g["InverseBasisMatrix"] = ExteriorMatrix[MatrixInverse[g["VectorBasis"]]]

g_GeometricAlgebra["MultiplicationTensor"] := g["MultiplicationTensor"] = With[{indices = g["Indices"], metric = g["MetricSignature"]}, {index = PositionIndex[indices]},
    SparseArray[Outer[SparseArray[Normal @ KeyMap[Lookup[index, Key[#]] &, multiplyIndices[#1, #2, metric]], Length[indices]] &, indices, indices, 1]]
]

g_GeometricAlgebra["MetricMultiplicationTensor"] := g["MetricMultiplicationTensor"] = With[{a = Transpose @ g["BasisMatrix"], b = Transpose @ g["InverseBasisMatrix"]},
    SparseArray[Transpose[b . Transpose[b . g["MultiplicationTensor"]]] . a]
]

g_GeometricAlgebra["ExomorphismMatrix"] := g["ExomorphismMatrix"] =
    SparseArray @ With[{metric = g["Metric"]}, Wedge[##]["Coordinates"] & @@@ Replace[Map[Grade[metric[[All, #]], 1, g] &, g["Indices"], {2}], {} -> {g[]}, 1]]

g_GeometricAlgebra["AntiExomorphismMatrix"] := g["AntiExomorphismMatrix"] = Transpose @ SparseArray[UnderBar[Bulk[OverBar[#]]]["Coordinates"] & /@ g["Basis"]]


Bulk[v_Multivector] := With[{g = GeometricAlgebra[v]}, Multivector[g["ExomorphismMatrix"] . v["Coordinates"], g]]

v_Multivector["Bulk"] := Bulk[v]

Weight[v_Multivector] := With[{g = GeometricAlgebra[v]}, Multivector[g["AntiExomorphismMatrix"] . v["Coordinates"], g]]

v_Multivector["Weight"] := Weight[v]

v_Multivector["BulkDual" | "RightBulkDual"] := RightBulkDual[v]

v_Multivector["LeftBulkDual"] := LeftBulkDual[v]

v_Multivector["WeightDual" | "RightWeightDual"] := RightWeightDual[v]

v_Multivector["LeftWeightDual"] := LeftWeightDual[v]

RightBulkDual[v_] := OverBar[Bulk[v]]

RightWeightDual[v_] := OverBar[Weight[v]]

LeftBulkDual[v_] := UnderBar[Bulk[v]]

LeftWeightDual[v_] := UnderBar[Weight[v]]

BulkDual = RightBulkDual

WeightDual = RightWeightDual


FlatPart[v_Multivector] := Multivector[KeySelect[v["Association"], Not @* FreeQ[- v["NegativeDimension"]]], GeometricAlgebra[v]]

RoundPart[v_Multivector] := Multivector[KeySelect[v["Association"], FreeQ[- v["NegativeDimension"]]], GeometricAlgebra[v]]

RoundBulk[v_Multivector] := Multivector[KeySelect[v["Association"], FreeQ[v["NonNegativeDimension"] | - v["NegativeDimension"]]], GeometricAlgebra[v]]

RoundWeight[v_Multivector] := Multivector[KeySelect[v["Association"], ! FreeQ[#, v["NonNegativeDimension"]] && FreeQ[#, - v["NegativeDimension"]] &], GeometricAlgebra[v]]

FlatBulk[v_Multivector] := Multivector[KeySelect[v["Association"], FreeQ[#, v["NonNegativeDimension"]] && ! FreeQ[#, - v["NegativeDimension"]] &], GeometricAlgebra[v]]

FlatWeight[v_Multivector] := Multivector[KeySelect[v["Association"], ! FreeQ[#, v["NonNegativeDimension"]] && ! FreeQ[#, - v["NegativeDimension"]] &], GeometricAlgebra[v]]


Carrier[v_Multivector] := Wedge[v, GeometricAlgebra[v]["Infinity"]]

Cocarrier[v_Multivector] := Wedge[WeightDual[v], GeometricAlgebra[v]["Infinity"]]

Container[v_Multivector] := Wedge[v, WeightDual[Carrier[v]]]

Partner[v_Multivector] := Vee[WeightDual[v]["Container"], v["Carrier"]]

v_Multivector["FlatPart"] := FlatPart[v]

v_Multivector["RoundPart"] := RoundPart[v]

v_Multivector["RoundBulk"] := Bulk[v]

v_Multivector["FlatBulk"] := FlatBulk[v]

v_Multivector["RoundWeight"] := Weight[v]

v_Multivector["FlatWeight"] := FlatWeight[v]

v_Multivector["Carrier"] := Carrier[v]

v_Multivector["Cocarrier"] := Cocarrier[v]

v_Multivector["Center"] := Vee[Cocarrier[v], v]

v_Multivector["Container"] := Container[v]

v_Multivector["Partner"] := Partner[v]


switchDualSide[v_Multivector] :=
    Multivector[
        MapThread[Function[{signs, x}, With[{coords = DualCoordinates[x]}, Dual @@ (Take[signs, Length[coords]] coords)], HoldAllComplete], {antiProductSigns[v["Dimension"], v["CoordinateDimension"]], Normal @ v["Coordinates"]}],
        v["GeometricAlgebra"]
    ]

g_GeometricAlgebra["MultiplicationTable"] := ResourceFunction["GridTableForm"][
    Map[Multivector[#, g] &, g["MultiplicationTensor"], {2}],
    TableHeadings -> {g["Basis"], g["Basis"]}
]

g_GeometricAlgebra["MetricMultiplicationTable"] := ResourceFunction["GridTableForm"][
    Map[Multivector[#, g] &, g["MetricMultiplicationTensor"], {2}],
    TableHeadings -> {g["Basis"], g["Basis"]}
]


GeometricProduct[v_Multivector, w_Multivector] := Block[{
    g = largestGeometricAlgebra[v, w], x, y, m
},
    x = ConvertGeometricAlgebra[v, g];
    y = ConvertGeometricAlgebra[w, g];
    m = Flatten[g["MetricMultiplicationTensor"], 1];
    Switch[{v["Orientation"], w["Orientation"]},
        {Left, Left},
            Multivector[Transpose[m] . Flatten[Outer[coordinateTimes, x["Coordinates"], y["Coordinates"], 1], 1], g],
        _,
            Multivector[coordinateTimes[#, y] & /@ x["Coordinates"], g, Right]
    ][Identity]
]

GeometricProduct[v_List, w_] := GeometricProduct[#, w] & /@ v

GeometricProduct[v_, w_List] := GeometricProduct[v, #] & /@ w

GeometricProduct[v_Multivector, w : Except[_Multivector]] := GeometricProduct[v, Grade[w, 0, GeometricAlgebra[v]]]

GeometricProduct[v : Except[_Multivector], w_Multivector] := GeometricProduct[Grade[v, 0, GeometricAlgebra[w]], w]

GeometricProduct[x_, y_] := x * y

GeometricProduct[left___, v_Multivector, right___] := Fold[GeometricProduct, {left, v, right}]


GeometricProduct[] := Multivector[{1}, {0, 0}]


Multivector /: Times[vs__Multivector] := GeometricProduct[vs]


Multivector /: Power[v_Multivector, n_Integer] := If[n < 0, Power[Inverse[v], -n], Nest[GeometricProduct[#, v] &, identityMultivector[v], n]]


Multivector /: Equal[left___, v_Multivector, right___] := With[{g = GeometricAlgebra[v]}, And @@ MapThread[Equal, Normal /@ Map[ConvertGeometricAlgebra[Multivector[#], g] &,  {left, v, right}]]]

Multivector /: Unequal[left___, v_Multivector, right___] := ! Equal[left, v, right]


Multivector /: (f_Symbol ? elementwiseFunctionQ)[v_Multivector, args___] := v[Map[f[#, args] &]]


Multivector /: N[v_Multivector ? MultivectorQ, args___] := With[{coords = N[v["Coordinates"], args]}, Multivector[coords, v["GeometricAlgebra"]] /; coords =!= v["Coordinates"]]

SetAttributes[Multivector, NHoldAll]


(* Tensor product *)

Multivector /: TensorProduct[v_Multivector, w_Multivector] := Block[{
    p, q, r
},
    {p, q, r} = v["Signature"];
    GeometricProduct[v,
        Multivector[
            KeyMap[# /. {i_ ? Positive :> i + p, i_ ? Negative :> i - q} &, w["Association"]],
            GeometricAlgebra[{p, q} + w["Signature"]]
        ]
    ]
]


(* infix notation *)

Multivector /: NonCommutativeMultiply[left___, v_Multivector, right___] := GeometricProduct[left, v, right]


(* Products and contractions *)

AntiGeometricProduct[vs__] := OverBar[GeometricProduct @@ UnderBar /@ {vs}]


gradeProduct[v_Multivector, w_Multivector] := Outer[GeometricProduct, GradeList[v], GradeList[w]]

gradeFunctionContraction[f_, vs__Multivector] := Fold[Total[MapIndexed[Grade[#1, f[#2 - 1]] &, gradeProduct[##], {2}], 2] &, {vs}]

gradeFunctionContraction[f_, left___, v_Multivector, right___] := gradeFunctionContraction[f, ##] & @@ (If[MultivectorQ[#], #, Grade[#, 0, GeometricAlgebra[v]]] & /@ {left, v, right})

LeftContraction[vs__] := gradeFunctionContraction[Apply[Subtract] @* Reverse, vs]

RightContraction[vs__] := gradeFunctionContraction[Apply[Subtract], vs]

DotProduct[vs__] := gradeFunctionContraction[Abs @* Apply[Subtract], vs]

Multivector /: Dot[left___, v_Multivector, right___] := DotProduct[left, v, right]

WedgeProduct[vs__] := gradeFunctionContraction[Apply[Plus], vs]

Multivector /: Wedge[left___, v_Multivector, right___] := WedgeProduct[left, v, right]

AntiWedgeProduct[vs__] := OverBar[Wedge @@ UnderBar /@ {vs}]

Multivector /: Vee[left___, v_Multivector, right___] := AntiWedgeProduct[left, v, right]

CrossProduct[vs__] := UnderBar[Wedge[vs]]

Multivector /: Cross[left___, v_Multivector, right___] := CrossProduct[left, v, right]

ScalarProduct[vs__] := Grade[GeometricProduct[vs], 0]

AntiDotProduct[vs__] := OverBar[Dot @@ UnderBar /@ {vs}]

InnerProduct[v_Multivector, w_Multivector] := With[{g = largestGeometricAlgebra[v, w]},
    Multivector[Multivector[w, g]["Coordinates"] . g["ExomorphismMatrix"] . Multivector[v, g]["Coordinates"], g][Identity]
]

AntiInnerProduct[v_Multivector, w_Multivector] := With[{g = largestGeometricAlgebra[v, w]},
    Grade[{Multivector[w, g]["Coordinates"] . g["AntiExomorphismMatrix"] . Multivector[v, g]["Coordinates"]}, -1, g][Identity]
]

(* AntiInnerProduct[v_Multivector, w_Multivector] := OverBar[InnerProduct[UnderBar[v], UnderBar[w]]] *)

RightInteriorProduct[a_Multivector, b_Multivector] := Vee[a, OverBar[b]]

LeftInteriorProduct[a_Multivector, b_Multivector] := Vee[UnderBar[a], b]

RightInteriorAntiProduct[a_Multivector, b_Multivector] := Wedge[a, OverBar[b]]

LeftInteriorAntiProduct[a_Multivector, b_Multivector] := Wedge[UnderBar[a], b]


BulkExpansion[v_Multivector, w_Multivector] := Wedge[v, RightBulkDual[w]]

WeightExpansion[v_Multivector, w_Multivector] := Wedge[v, RightWeightDual[w]]

BulkContraction[v_Multivector, w_Multivector] := Vee[v, RightBulkDual[w]]

WeightContraction[v_Multivector, w_Multivector] := Vee[v, RightWeightDual[w]]

MultivectorDistance[v_Multivector, w_Multivector] := Vee[v, w] + WeightNorm[Wedge[v, Attitude[w]]]

MultivectorCosAngle[v_Multivector, w_Multivector] := BulkNorm[WeightContraction[v, w]] + Vee[WeightNorm[v], WeightNorm[w]]


(* Inversions *)

reverseIndexCoordinate[g_GeometricAlgebra, indexPos_, x_] := Block[{newIndex, sign}, 
    {newIndex, sign} = orderIndexWithSign[Reverse[Extract[g["Indices"], indexPos]], g["Dimension"]];
    newIndex -> sign x
]

v_Multivector["Reverse"] := With[{g = GeometricAlgebra[v]},
    Multivector[
        Association[reverseIndexCoordinate[g, #1, #2] & @@@ Most @ ArrayRules @ v["Coordinates"]],
        g
    ]
]

OverTilde[v_Multivector] ^:= v["Reverse"]

Multivector /: Reverse[v_Multivector] := v["Reverse"]

AntiReverse[v_Multivector] := v["Reverse"]["DoubleComplement"]

v_Multivector["AntiReverse"] := AntiReverse[v]


Involute[v_Multivector] := mapCoordinates[((-1) ^ # & @* Length /@ v["Indices"]) # &, v]

v_Multivector["Involute"] = Involute[v]


v_Multivector["Conjugate"] = v["Involute"]["Reverse"]

(SuperStar | Conjugate)[v_Multivector] ^:= v["Conjugate"]


LeftComplement[v_Multivector] := With[{i = v["PseudoscalarIndex"]},
     Multivector[
        Association @ KeyValueMap[
            Function[{j, x}, With[{k = DeleteElements[i, j]}, k -> permutationSignature[i, Join[k, j]] x]],
            v["Association"]
        ],
        GeometricAlgebra[v]
    ]
]

v_Multivector["LeftComplement"] := LeftComplement[v]

RightComplement[v_Multivector] :=  With[{i = v["PseudoscalarIndex"]},
     Multivector[
        Association @ KeyValueMap[
            Function[{j, x}, With[{k = DeleteElements[i, j]}, k -> permutationSignature[i, Join[j, k]] x]],
            v["Association"]
        ],
        GeometricAlgebra[v]
    ]
]

v_Multivector["RightComplement"] := RightComplement[v]


Multivector /: UnderBar[v_Multivector] := v["LeftComplement"]

Multivector /: OverBar[v_Multivector] := v["RightComplement"]


v_Multivector["DoubleComplement"] := v["RightComplement"]["RightComplement"]

v_Multivector["Squared"] = GeometricProduct[v, v["Involute"]]


Sandwich[v_Multivector, w_Multivector] := - GeometricProduct[w, v, Inverse[w]]

AntiSandwich[v_Multivector, w_Multivector] := - AntiGeometricProduct[w, v, UnderBar[Inverse[OverBar[w]]]]

Multivector /: Commutator[v_Multivector, w_Multivector] := GeometricProduct[v, w] - GeometricProduct[w, v]

AntiCommutator[v_Multivector, w_Multivector] := GeometricProduct[v, w] + GeometricProduct[w, v]


(* Projections *)

Multivector /: Projection[v_Multivector, w_Multivector] := GeometricProduct[w, v . w]


Rejection[v_Multivector, w_Multivector] := GeometricProduct[Wedge[v, w], w]


OrthoProjection[v_Multivector, w_Multivector] := Vee[w, WeightExpansion[v, w]]

OrthoAntiprojection[v_Multivector, w_Multivector] := Wedge[w, WeightContraction[v, w]]

CentralProjection[v_Multivector, w_Multivector] := Vee[w, BulkExpansion[v, w]]

CentralAntiprojection[v_Multivector, w_Multivector] := Wedge[w, BulkContraction[v, w]]


(* Inverse *)

Multivector /: Inverse[v_Multivector] := MultivectorFunction[# ^ -1 &, v]

v_Multivector["Inverse"] = Inverse[v]

Multivector /: Divide[v_, w_Multivector] := GeometricProduct[Multivector[v, w["GeometricAlgebra"]], Inverse[w]]


(* Root and Power *)

Multivector /: Sqrt[v_Multivector] := v ^ (1 / 2)

Multivector /: Root[v_Multivector, n_Integer] := MultivectorFunction[Power[#, 1 / n] &, v]

Multivector /: Power[v_Multivector, p_Rational] := With[{n = Numerator[p], d = Denominator[p]}, Root[v ^ n, d]]

Multivector /: Power[v_Multivector, x_] := MultivectorPower[v, x]


(* D *)

Multivector /: D[v_Multivector, x_] := v[Map[D[#, x] &]]


(* Grade *)

Grade[v_Multivector, n_Integer] /; n < 0 || n > v["Dimension"] := zeroMultivector[v]

Grade[v_Multivector, n_Integer] := With[{vector = gradeVector[v["GeometricAlgebra"], n]}, mapCoordinates[# * vector &, v]]

Grade[v_Multivector] := With[{grades = Length /@ Extract[v["Indices"], SparseArray[v["Coordinates"]]["ExplicitPositions"]]},
    If[Equal @@ grades, First[grades], Indeterminate]
]

GradeList[v_Multivector] := Grade[v, #] & /@ Range[0, v["Dimension"]]

Grade[coords_List, n_Integer, args___] := Block[{
    G = GeometricAlgebra[args], d,
    skipDimension, bladeDimension
},
    d = G["Dimension"];
    k = Mod[n, d + 1];
    skipDimension = binomialSum[d, k - 1];
    bladeDimension = Binomial[d, k];
    Multivector[SparseArray[MapIndexed[Function[{x, i}, skipDimension + i -> x, HoldAllComplete], Take[coords, UpTo[bladeDimension]]], G["Order"]], G]
]

Grade[x_, n_Integer, args___] := Grade[{x}, n, args]

Grade[v_Multivector, grades : {__Integer}] := Total[Grade[v, #] & /@ grades]

Grade[v_Multivector, "Even"] := Total[Grade[v, #] & /@ Range[0, v["Dimension"], 2]]

Grade[v_Multivector, "Odd"] := Total[Grade[v, #] & /@ Range[1, v["Dimension"], 2]]


AntiGrade[v_Multivector] := v["Dimension"] - Grade[v]

AntiGrade[args___] := Grade[args]["Dual"]


v_Multivector["Grade", arg_] := Grade[v, arg]


(* Special multivectors *)

g_GeometricAlgebra["Scalar"] := Multivector[1, g]


pseudoscalar[g_GeometricAlgebra] := Multivector[<|g["PseudoscalarIndex"] -> 1|>, g]

pseudoscalar[v_Multivector] := pseudoscalar[GeometricAlgebra[v]]

pseudoscalar[] := pseudoscalar[GeometricAlgebra[]]

g_GeometricAlgebra["Pseudoscalar"] := pseudoscalar[g]


g_GeometricAlgebra["Nilpotent", n_Integer] := With[{
    i = Abs[n]
},
    ConvertGeometricAlgebra[Multivector[<|{i} -> 1 / 2, {-i} -> Sign[n] 1 / 2|>, g["BalancedAlgebra"]], g]
]


g_GeometricAlgebra["Idempotent", n_Integer] := GeometricProduct[g["Nilpotent", - n], g["Nilpotent", n]]


g_GeometricAlgebra["Origin"] := g[g["NonNegativeDimension"]]

g_GeometricAlgebra["Horizon"] := OverBar[g["Origin"]]

g_GeometricAlgebra["Infinity"] := g[- g["NegativeDimension"]]

Attitude[v_Multivector] := Vee[v, v["Horizon"]]

Support[v_Multivector] := OrthoProjection[v["Origin"], v]

Antisupport[v_Multivector] := CentralAntiprojection[v["Horizon"], v]


(* Duals *)

LeftDual[v_Multivector] := LeftContraction[v, pseudoscalar[v]["Reverse"]]

v_Multivector["LeftDual"] := LeftDual[v]


RightDual[v_Multivector] := RightContraction[pseudoscalar[v], v]

v_Multivector["RightDual"] := RightDual[v]


v_Multivector["Dual"] := LeftDual[v]


Multivector /: SuperDagger[v_Multivector] := v["Dual"]


(* Norms *)

v_Multivector["BulkNorm"] := BulkNorm[v]

BulkNorm[v_Multivector] := InnerProduct[v, v][Sqrt]

v_Multivector["WeightNorm" | "RadiusNorm"] := WeightNorm[v]

WeightNorm[v_Multivector] := AntiInnerProduct[v, v][Sqrt]

GeometricNorm[v_Multivector] := BulkNorm[v] + WeightNorm[v]

v_Multivector["Norm" | "GeometricNorm"] := GeometricNorm[v]

Multivector /: Norm[v_Multivector] := GeometricNorm[v]

\[LeftDoubleBracketingBar] v_Multivector \[RightDoubleBracketingBar] := GeometricNorm[v]

v_Multivector["Radius"] := v["RadiusNorm"] / WeightNorm[RoundPart[v]]

v_Multivector["CenterNorm"] := Sqrt[BulkNorm[RoundPart[v]] ^ 2 + WeightNorm[FlatPart[v]] ^ 2]

v_Multivector["CoordinateNorm"] := Norm[v["Coordinates"]]

v_Multivector["Normalize"] := v / v["Norm"]

Multivector /: Normalize[v_Multivector] := v["Normalize"]

WeightUnitize[v_Multivector] := v / WeightNorm[v]["Pseudoscalar"]

v_Multivector["Unitize" | "WeightUnitize"] := WeightUnitize[v]

Multivector /: (Unitize | OverHat)[v_Multivector] := WeightUnitize[v]

v_Multivector["Tr"] := v + v["Conjugate"]

Multivector /: Tr[v_Multivector] := v["Tr"]


v_Multivector["Det"] := GeometricProduct[v, v["Conjugate"]]

Multivector /: Det[v_Multivector] := v["Det"]

\[LeftBracketingBar] v_Multivector \[RightBracketingBar] := v["Det"]


(* *)

RandomMultivector[arg_, g_GeometricAlgebra] := Multivector[RandomReal[arg, g["Order"]], g]

RandomMultivector[g_GeometricAlgebra] := RandomMultivector[{-1, 1}, g]

RandomMultivector[arg_, n_Integer, g_GeometricAlgebra] := Table[RandomMultivector[arg, g], n]

RandomMultivector[arg_, args___] := RandomMultivector[arg, GeometricAlgebra[args]]

RandomMultivector[args___, n_Integer] := Table[RandomMultivector[args], n]

RandomMultivector[args___] := RandomMultivector[GeometricAlgebra[args]]


(* Formatting *)

$DefaultMultivectorFormatFunction = Function[index,
    If[ index === {},
        "", (* don't display zero coefficient terms *)
        Subscript["e", Row[If[# > 0, #, UnderBar[Abs[#]]] & /@ index, "\[InvisibleComma]"]]
    ]
]


geometricIndexFormat[g_GeometricAlgebra, index_] := With[{format = g["FormatIndex"]},
    Switch[format,
        Automatic,
        $DefaultMultivectorFormatFunction[index]
        ,
        "Positive",
        $DefaultMultivectorFormatFunction[positiveIndex[index, g["Signature"]] - 1]
        ,
        _Function,
        format[index]
        ,
        _,
        index /. Append[_ -> $DefaultMultivectorFormatFunction[index]] @ DeleteCases[Except[_Rule]] @ Developer`ToList[format]
    ]
]

geometricIndexFormat[g_GeometricAlgebra, {indices__List}] := geometricIndexFormat[g, #] & /@ {indices}

geometricIndexFormat[g_GeometricAlgebra] := geometricIndexFormat[g, g["Indices"]]

geometricIndexFormat[index_] := geometricIndexFormat[Lookup[Options[Multivector], "GeometricAlgebra"], index]

geometricIndexFormat[] := geometricIndexFormat[Lookup[Options[Multivector], "GeometricAlgebra"]]


holdSparseArray[HoldPattern[a : SparseArray[{}, ___]]] := a
holdSparseArray[HoldPattern[SparseArray[{xs__}, opts___]]] := SparseArray[List @@ MapAt[Hold, Hold[xs], {All, 2}], opts]

Multivector /: MakeBoxes[v : Multivector[coords_, __] /; MultivectorQ[Unevaluated[v]], form_] := Block[{
    g = v["GeometricAlgebra"],
    orientation = v["Orientation"],
    holdCoords,
    rules,
    nonZeroPositions,
    d, n,
    indices, metric,
    display, interpret,
    gBox, boxes
},
    gBox = ToBoxes[g, form];
    d = g["Dimension"];
    indices = g["OrderedIndices"];
    metric = g["Metric"];
    holdCoords = Which[
        SparseArrayQ[Unevaluated[coords]], (* don't hold elements of a SparseArray object *)
        Map[Hold, coords]
        ,
        MatchQ[Unevaluated[coords], _SparseArray], (* hold each element of a SparseArray constructor *)
        holdSparseArray[Unevaluated[coords]]
        ,
        True,
        Map[Hold, Unevaluated[coords]] (* hold elements of a List *)
    ];
    holdCoords = Extract[holdCoords, Lookup[PositionIndex[g["Indices"]], SortBy[#, Mod[#, d + 1] &] & /@ indices, Nothing]];
    rules = Cases[ArrayRules[holdCoords], ({i_Integer} -> c_) /; If[c != Hold[0], True, False, ! MatchQ[c, Hold[w_Multivector] /; w == 0]] :> {i, c}];
    nonZeroPositions = rules[[All, 1]];
    n = Length @ nonZeroPositions;
    boxes = ReleaseHold @ Map[
            Apply[
                Function[{i, holdCoord}, If[ i > 1,
                    Function[x, With[{coord = x * orderAndContract[indices[[i]], metric][[2]]}, Switch[coord,
                        1, InterpretationBox["\[InvisibleSpace]", coord],
                        -1, InterpretationBox["-", coord],
                        _, If[MatchQ[coord, _Multivector | _Dual], RowBox[{"(", ToBoxes[coord, form], ")"}], Parenthesize[coord, form, Times]]
                    ]], HoldAllComplete] @@ holdCoord,
                    Function[x, MakeBoxes[x, form], HoldAllComplete] @@ holdCoord
                ], HoldRest]
            ],
            rules
        ];
    display = RowBox @ If[ n > 0,
        Riffle[
            MapThread[
                RowBox[If[orientation === Right, Reverse, Identity] @ {
                    #1,
                    StyleBox[ToBoxes[geometricIndexFormat[g, #2], form], "ShowStringCharacters" -> False]
                }] &,
                { Slot /@ Range[n], indices[[nonZeroPositions]]}
            ],
        "+"
        ],
        {0} (* all zeros displayed as just zero *)
    ];
    interpret = RowBox[{"Multivector", "[",
        "SparseArray", "[", "{",
            Sequence @@ If[n > 0, 
                Riffle[MapThread[RowBox[{ToBoxes[#1, form], "->", #2}] &, {nonZeroPositions, Slot /@ Range[n]}], ","],
                {}
            ],
            "}", ",", ToBoxes[g["Order"], form],
        "]",
        ",",
        gBox, "]"
    }];
    TemplateBox[
        boxes,
        "Multivector",
        DisplayFunction -> (Evaluate @ display &),
        InterpretationFunction -> (Evaluate @ interpret &),
        Tooltip -> RowBox[{"Multivector", " ", gBox}],
        Editable -> True
    ]
]


(* Frontend *)

binaryOperationBox[f_String, infix_String] := TemplateBox[
    {"\[Placeholder]", "\[Placeholder]"},
    f,
    InterpretationFunction -> (RowBox[{f, "[", #1, ",", #2, "]"}] &),
    DisplayFunction -> (RowBox[{#1, infix, #2}] &)
]

UsingFrontEnd[
    SetOptions[EvaluationNotebook[],
        InputAliases -> {
            "gp" -> binaryOperationBox["GeometricProduct", "⟑"],
            "agp" -> binaryOperationBox["AntiGeometricProduct", "⟇"],
            "wedge" -> binaryOperationBox["WedgeProduct", "\[Wedge]"],
            "awedge" -> binaryOperationBox["AntiWedgeProduct", "\[Vee]"],
            "dot" -> binaryOperationBox["InnerProduct", "\[FilledSmallCircle]"],
            "adot" -> binaryOperationBox["AntiInnerProduct", "\[SmallCircle]"]
        }
    ]
]
