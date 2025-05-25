Package["Wolfram`GeometricAlgebra`"]

PackageExport[ExteriorMatrix]

PackageScope[identityMatrix]
PackageScope[MatrixInverse]
PackageScope[elementwiseFunctionQ]
PackageScope[numericFunctionQ]
PackageScope[hasDefinitionsQ]
PackageScope[permutationSignature]
PackageScope[mergeOptions]
PackageScope[mergeGeometricAlgebra]
PackageScope[largestGeometricAlgebra]
PackageScope[constantFunction]
PackageScope[functionBody]
PackageScope[reduceFunctions]
PackageScope[mapCoordinates]
PackageScope[coordinateTimes]
PackageScope[solveCoordinates]
PackageScope[dotIndices]
PackageScope[orderIndexWithSign]
PackageScope[contractBlade]
PackageScope[orderAndContract]
PackageScope[multiplyIndices]
PackageScope[binomialSum]
PackageScope[gradeVector]
PackageScope[indexSpan]
PackageScope[normalIndex]
PackageScope[positiveIndex]


elementwiseFunctionQ = MatchQ[Simplify | FullSimplify | Expand | ComplexExpand | TrigExpand | FunctionExpand | Together | ExpToTrig | TrigToExp | Chop]

numericFunctionQ[f_] := MatchQ[f, _Symbol] && MemberQ[Attributes[f], NumericFunction]


hasDefinitionsQ[f_Symbol] := GeneralUtilities`HasDefinitionsQ[f] || Length[Attributes[f]] > 0

hasDefinitionsQ[f_] := GeneralUtilities`HasDefinitionsQ[f]


permutationSignature[x_List, y_List] := permutationSignature[FindPermutation[x, y]]

permutationSignature[perm_ ? PermutationCyclesQ] := Apply[Times, (-1) ^ (Length /@ First[perm] - 1)]


identityMatrix[0] := {{}}

identityMatrix[n_Integer] := IdentityMatrix[n]


ExteriorMatrix[{{}}] := {{1}}

ExteriorMatrix[matrix_ ? SquareMatrixQ] := With[{n = Length[matrix]},
	BlockDiagonalMatrix @ Table[
		With[{subsets = Subsets[Range[n], {k}]},
			SparseArray @ Map[columns |->
				Total[Signature[#] * Times @@ MapThread[Part, {columns, #}] & /@ Permutations[#]] & /@ subsets,
				Map[matrix[[All, #]] &, subsets, {2}]
			]
		],
		{k, 0, n}
	]
]

MatrixInverse[{{}}] := {{}}

MatrixInverse[matrix_ ? SquareMatrixQ] := PseudoInverse[matrix]


mergeOptions[opts_, drop_: False] := Sequence @@ Normal @ Merge[If[drop, DeleteCases[Join @@ opts, _ -> Automatic], Join @@ opts], First]


mergeGeometricAlgebra[vs__Multivector] := GeometricAlgebra[
    MapThread[Max, #["GeometricAlgebra"]["Signature"] & /@ {vs}],
    mergeOptions[Normal @ KeyDrop[Options[#["GeometricAlgebra"]], {"Signature", If[Equal @@ Through[{vs}["Dimension"]], Nothing, "VectorBasis"]}] & /@ {vs}, True]
]

largestGeometricAlgebra[vs__Multivector] := largestGeometricAlgebra[{vs}]

largestGeometricAlgebra[vs : {__Multivector}] := First @ MaximalBy[GeometricAlgebra /@ vs, #["Dimension"] &]


constantFunction[f_Function] := f
constantFunction[x_] := Function[x]


functionBody[Function[body_]] := body
functionBody[x_] := x


reduceFunctions[expr_] := Activate @ FixedPoint[Function[x, ReplaceRepeated[x, {
    HoldPattern[(f: Function[x_])[y_]] :> With[{e = Inactivate[f[y], D]}, Function[e] /; True],
    f: HoldPattern[Function[x_]] /; FreeQ[Hold[x], _Slot, {0, \[Infinity]}] :> x,
    (* f: HoldPattern[Function[{xs__}, x_]] /; FreeQ[x, Alternatives[xs], {0, \[Infinity]}]:> x,*)
    (* HoldPattern[Function[x_]] :> With[{e = Inactivate[x, D]}, Function[e] /; True],*)
    HoldPattern[Function[Function[x_]]] :> With[{e = Simplify @ Inactivate[x, D]}, Function[e] /; True],
    HoldPattern[Plus[xs___, f_Function, ys___]] :> With[{e = Plus @@ (functionBody /@ Inactivate[{xs, f, ys}, D])}, Function[e] /; True],
    HoldPattern[Times[xs___, f_Function, ys___]] /; FreeQ[{xs, ys}, _Function, {0, \[Infinity]}] :> With[{e = Times @@ (functionBody /@ Inactivate[{xs, f, ys}, D])}, Function[e] /; True]
}], HoldAllComplete], expr]


mapCoordinates[f_, v_Multivector] := Multivector[reduceFunctions[f[v["Coordinates"]]], v["GeometricAlgebra"]]


coordinateTimes[f: Function[x_], Function[y_]] := reduceFunctions[Function[f[y]]]

coordinateTimes[f_Function, y_] := f[y]

coordinateTimes[x_, Function[y_]] := reduceFunctions[Function[GeometricProduct[x, y]]]

coordinateTimes[v_, w_] := GeometricProduct[v, w]


solveCoordinates[f_Function, A_GeometricAlgebra] := Module[{w, sol},
    Block[{x},
        w = Array[Subscript[x, #] &, A["Order"]];
        sol = Solve[Thread[Normal[f[Multivector[w, A]]] == Normal[A["Zero"]]], w];
        If[ Length[sol] == 0 || Not[FreeQ[sol, ComplexInfinity | Indeterminate, Infinity]],
            $Failed,
            w /. First[sol] /. Thread[w -> 0]
        ]
    ]
]


dotIndices[{}, __] := 1
dotIndices[_, {}, _] := 1
dotIndices[u_, v_, g_] := Det[Outer[g[[##]] &, u, v]]

orderIndexWithSign[index_List, n_Integer] := With[{order = OrderingBy[index, Mod[#, n + 1] &]}, {index[[order]], Signature @ order}];

contractBlade[index_, g_] := Block[{newIndex, squares},
    squares = First[Reap[newIndex = SequenceReplace[index, {x_, x_} :> (Sow[x]; Nothing)]][[2]], {}];
    {newIndex, Times @@ If[VectorQ[g], g[[squares]], g[[#, #]] & /@ squares]}
]

orderAndContract[index_, g_] := ({j, x} |-> {#1, x * #2} & @@ contractBlade[j, g]) @@ orderIndexWithSign[index, Length[g]]

orderAndContractBlades[g_][indices_] := Merge[Total] @ KeyValueMap[{k, x} |-> #1 -> x * #2 & @@ orderAndContract[k, g], indices]

multiplyIndices[uu : {___Integer}, vv : {___Integer}, g_ ? SquareMatrixQ] := Block[{
	n = Length[g], x, y, u, v, j, k, sigma, tau
},
	{u, x} = orderAndContract[uu, g];
	{v, y} = orderAndContract[vv, g];
	j = Length[u];
	k = Length[v];
	sigma = Permutations[v];
	tau = Permutations[u];
	x * y * DeleteCases[0] @ orderAndContractBlades[g] @ Association @ Table[
		Join[#2[[;; j - i]], #1[[i + 1 ;; k]]] ->
			Signature[Mod[#1, n + 1]] * Signature[Mod[#2, n + 1]] * dotIndices[Reverse[#2[[j - i + 1 ;; j]]], #1[[;; i]], g] & @@@
			Tuples[{
				Select[sigma, Less @@ #[[;; i]] && Less @@ #[[i + 1 ;; k]] &],
				Select[tau, Less @@ #[[;; j - i]] && Less @@ #[[j - i + 1 ;; j]] &]
			}],
		{i, 0, Min[j, k]}
	]
]

multiplyIndices[u : {___Integer}, v : {___Integer}, g_ ? VectorQ] := <|#1 -> #2|> & @@ orderAndContract[Join[u, v], g]


binomialSum[n_Integer, k_Integer] := binomialSum[n, k] = Sum[Binomial[n, i], {i, 0, k}]


gradeVector[A_GeometricAlgebra, k_Integer] := gradeVector[A["Dimension"], A["Order"], k]

gradeVector[n_, d_, k_] := gradeVector[n, d, k] = SparseArray[
    Thread[Range[binomialSum[n, k - 1] + 1, binomialSum[n, k]] -> 1],
    d
]


indexSpan[v_Multivector, n_Integer] :=
    binomialSum[v["GeometricAlgebra"]["Dimension"], n - 1] + 1 ;; binomialSum[v["GeometricAlgebra"]["Dimension"], n]

indexSpan[_Multivector, All] := All


positiveIndex[index_Integer, {p_, q_, _}] := 1 + If[index >= 0, index, Min[- index, q] + p]

positiveIndex[indices : {___Integer}, signature_] := positiveIndex[#, signature] & /@ indices


normalIndex[index_Integer, {p_, q_, r_}] := If[index < 0, Max[index, - q], If[index > p + r, Max[p + r - index, - q], Min[index, p + r]]]

normalIndex[indices : {___Integer}, signature_] := normalIndex[#, signature] & /@ indices

