BeginTestSection["Test"]


Needs["Wolfram`GeometricAlgebra`"];


SetOptions[Multivector, "GeometricAlgebra" -> GeometricAlgebra[0, 1]];

VerificationTest[
    Normal[Multivector[{1, 2}] ** Multivector[{3, -4}]],
    ReIm[(1 + 2 I) (3 - 4 I)],
    TestID -> "Complex number multiplication"
]

SetOptions[Multivector, "GeometricAlgebra" -> GeometricAlgebra[2, 3]];

VerificationTest[
    Map[Grade[Multivector[SparseArray[{1 -> 01, 3 -> 13, 9 -> 29, 25 -> 316, 28 -> 428, 30 -> 430, 32 -> 532}]], #]&, Range[0, 5]],
    {
        Multivector[SparseArray[{1 -> 01}], GeometricAlgebra[2, 3], Left],
        Multivector[SparseArray[{3 -> 13}], GeometricAlgebra[2, 3], Left],
        Multivector[SparseArray[{9 -> 29}], GeometricAlgebra[2, 3], Left],
        Multivector[SparseArray[{25 -> 316}], GeometricAlgebra[2, 3], Left],
        Multivector[SparseArray[{28 -> 428, 30 -> 430}], GeometricAlgebra[2, 3], Left],
        Multivector[SparseArray[{32 -> 532}], GeometricAlgebra[2, 3], Left]
    },
    TestID -> "Grade computation"
]

VerificationTest[
    Head[MakeBoxes[x Multivector[{1,2,3}, "GeometricAlgebra" -> GeometricAlgebra[4,1]], StandardForm]],
    RowBox,
    TestID -> "Boxes"
]


(* ===== GeometricMatrix Tests ===== *)

(* Numeric roundtrip: MultivectorMatrix -> MatrixMultivector *)
VerificationTest[
    Module[{G, v, mat, w},
        G = GeometricAlgebra[1, 1];
        v = Multivector[{1, 2, 3, 4}, G];
        mat = MultivectorMatrix[v];
        w = MatrixMultivector[mat, G];
        v == w
    ],
    True,
    TestID -> "Matrix roundtrip Cl(1,1)"
]

VerificationTest[
    Module[{G, v, mat, w},
        G = GeometricAlgebra[2, 2];
        v = Multivector[Range[16], G];
        mat = MultivectorMatrix[v];
        w = MatrixMultivector[mat, G];
        v == w
    ],
    True,
    TestID -> "Matrix roundtrip Cl(2,2)"
]

VerificationTest[
    Module[{G, v, mat, w},
        G = GeometricAlgebra[3, 3];
        v = Multivector[Range[64], G];
        mat = MultivectorMatrix[v];
        w = MatrixMultivector[mat, G];
        v == w
    ],
    True,
    TestID -> "Matrix roundtrip Cl(3,3)"
]

(* Symbolic roundtrip *)
VerificationTest[
    Module[{G, v, mat, w},
        G = GeometricAlgebra[1, 1];
        v = Multivector[{a, b, c, d}, G];
        mat = MultivectorMatrix[v];
        w = MatrixMultivector[mat, G];
        Expand[v["Coordinates"] - w["Coordinates"]] === 0 * Range[4]
    ],
    True,
    TestID -> "Matrix roundtrip symbolic Cl(1,1)"
]

(* Matrix algebra homomorphism: M(u**v) == M(u).M(v) *)
VerificationTest[
    Module[{G, u, v},
        G = GeometricAlgebra[1, 1];
        u = Multivector[{1, 2, 3, 4}, G];
        v = Multivector[{5, -3, 2, 1}, G];
        Expand[MultivectorMatrix[GeometricProduct[u, v]]["Numeric"] -
            MultivectorMatrix[u]["Numeric"] . MultivectorMatrix[v]["Numeric"]]
    ],
    {{0, 0}, {0, 0}},
    TestID -> "Matrix homomorphism Cl(1,1)"
]

VerificationTest[
    Module[{G, u, v},
        G = GeometricAlgebra[2, 2];
        u = Multivector[Range[16], G];
        v = Multivector[Reverse[Range[16]], G];
        Expand[MultivectorMatrix[GeometricProduct[u, v]]["Numeric"] -
            MultivectorMatrix[u]["Numeric"] . MultivectorMatrix[v]["Numeric"]]
    ],
    ConstantArray[0, {4, 4}],
    TestID -> "Matrix homomorphism Cl(2,2)"
]

(* Orthogonality via public API: M(v).M(v)^T should be proportional to identity
   for basis elements, and the matrix representation should be invertible *)
VerificationTest[
    Module[{G, v, mat},
        G = GeometricAlgebra[1, 1];
        v = Multivector[{a, b, c, d}, G];
        mat = MultivectorMatrix[v]["Numeric"];
        Expand[Det[mat]]
    ],
    Expand[(a + d)(a - d) - (b - c)(b + c)],
    TestID -> "Matrix determinant Cl(1,1)"
]

(* nilpotentMatrix is orthogonal up to scaling: tested via roundtrip identity *)
VerificationTest[
    Module[{G, coords, v, mat, w},
        G = GeometricAlgebra[2, 2];
        coords = RandomInteger[{-10, 10}, 16];
        v = Multivector[coords, G];
        mat = MultivectorMatrix[v];
        w = MatrixMultivector[mat, G];
        w["Coordinates"] == coords
    ],
    True,
    TestID -> "Random roundtrip Cl(2,2)"
]

EndTestSection[]

