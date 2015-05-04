(* ::Package:: *)

(* ::Title:: *)
(*Sieve*)


(* ::Subtitle:: *)
(*Chip Hurst*)
(*ghurst@wolfram.com*)
(*2014*)


(* ::Subsubtitle:: *)
(*Load this package in M9... There are compile errors in M10.*)


(* ::Section::Closed:: *)
(*BeginPackage*)


BeginPackage["Sieve`"];

fastCompile::usage = "";

(* Sievers *)
Sieve::usage = "";
SieveFunction::usage = "";

(* Arithmetic functions over a range *)
PrimesInRange::usage = "";
PrimeTable::usage = "";
PrimeQTable::usage = "";
PrimePowerQTable::usage = "";
MoebiusMuTable::usage = "";
LeastPrimeFactorsTable::usage = "";
DivisorSigmaTable::usage = "";
EulerPhiTable::usage = "";
SquareFreeInRange::usage = "";
SquareFreeQTable::usage = "";
MangoldtLambdaTable::usage = "";
PrimeNuTable::usage = "";
PrimeOmegaTable::usage = "";
LiouvilleLambdaTable::usage = "";

(* Summatory functions *)
MertenM::usage = "";
SquareFreePi::usage = "";
DivisorSigmaSum::usage = "";
ChebyshevPsi::usage = "";
ChebyshevTheta::usage = "";
ChebyshevPsiSlow::usage = "";
ChebyshevThetaSlow::usage = "";
Prime\[Pi]::usage = "";

(* Misc. *)
Primorial::usage = "";
LeastPrimeFactor::usage = "";
SquareFree::usage = "";
MeisselMerten::usage = "";

Begin["`Private`"];


(* ::Text:: *)
(*TODO: 3 argument PrimePi, PrimeSum, DivisorSigmaSum, JordanTotient, what else??*)


(* ::Section::Closed:: *)
(*Compile*)


<<CCompilerDriver` (* for CCompilers *)
<<CompiledFunctionTools` (* for CompilePrint *)


$fastCompileOptions = Sequence[
	If[Length[CCompilers[]] > 0, CompilationTarget -> "C", Sequence @@ {}],
	Parallelization -> True,
	RuntimeOptions -> "Speed",
	CompilationOptions -> {"ExpressionOptimization" -> True, "InlineCompiledFunctions" -> True, "InlineExternalDefinitions"->True}
];


SetAttributes[fastCompile, HoldAllComplete];


fastCompile[vars_, code_, ops___] := ReleaseHold[Hold[Compile[vars, code, ops, ##]]&[$fastCompileOptions] /. {Mod[e_, 2] :> BitAnd[e, 1]}]


(* ::Section::Closed:: *)
(*Sievers*)


(* ::Subsection::Closed:: *)
(*Prime*)


SegmentedPrimeSieve = fastCompile[{{l, _Integer}, {hi, _Integer}, {\[CapitalDelta], _Integer}, {primes, _Integer, 1}},
	Module[{lo = Max[l, 2], S, sqrt = Round[Sqrt[hi]], p, st},
		S = Range[lo, hi];
		Do[
			p = primes[[i]];

			If[p > sqrt, Break[]];
			st = lo + Mod[-lo, p];

			If[st > hi, Continue[]];
			If[st == p, st += p];
			Do[
				S[[k]] = 0,
				{k, st - lo + 1, hi - lo + 1, p}
			],
			{i, 1, Length[primes]}
		];

		If[\[CapitalDelta] == 1,
			Select[S, Positive],
			Select[S[[1 ;; -1 ;; \[CapitalDelta]]], Positive]
		]
	]
];


(* ::Subsection::Closed:: *)
(*PrimeQ*)


SegmentedPrimeQSieve = fastCompile[{{lo, _Integer}, {hi, _Integer}, {\[CapitalDelta], _Integer}, {primes, _Integer, 1}},
	Module[{S, sqrt = Round[Sqrt[hi]], p, st},
		S = Table[1, {hi - lo + 1}];
		Do[
			p = primes[[i]];

			If[p > sqrt, Break[]];
			st = lo + Mod[-lo, p];

			If[st > hi, Continue[]];
			If[st == p, st += p];
			Do[
				S[[k]] = 0,
				{k, st - lo + 1, hi - lo + 1, p}
			],
			{i, 1, Length[primes]}
		];

		If[lo <= 1 <= hi, S[[2 - lo]] = 0];

		If[\[CapitalDelta] == 1,
			S,
			S[[1 ;; -1 ;; \[CapitalDelta]]]
		]
	]
];


(* ::Subsection::Closed:: *)
(*PrimePowerQ*)


SegmentedPrimePowerQSieve = fastCompile[{{lo, _Integer}, {hi, _Integer}, {\[CapitalDelta], _Integer}, {primes, _Integer, 1}},
	Module[{S, sqrt = Round[Sqrt[hi]], p, st, next},
		S = Table[-1, {hi - lo + 1}];
		Do[
			p = primes[[i]];

			If[p > sqrt, Break[]];
			st = Max[lo + Mod[-lo, p], 2p];

			If[st > hi, Continue[]];
			next = p^Max[2, IntegerLength[lo-1, p]];
			Do[
				If[k == next, 
					next *= p;
					Continue[]
				];
				S[[k - lo + 1]]++,
				{k, st, hi, p}
			],
			{i, 1, Length[primes]}
		];

		If[lo <= 1 <= hi, S[[2 - lo]] = 0];
		If[\[CapitalDelta] > 1, S = S[[1 ;; -1 ;; \[CapitalDelta]]]];

		1 - UnitStep[S]
	]
];


(* ::Subsection::Closed:: *)
(*MoebiusMu*)


SegmentedMoebiusMuSieve = fastCompile[{{lo, _Integer}, {hi, _Integer}, {\[CapitalDelta], _Integer}, {primes, _Integer, 1}},
	Module[{S = Table[1, {hi - lo + 1}], sqrt = Round[Sqrt[hi]], p, st},

		Do[
			p = primes[[i]];

			If[p > sqrt, Break[]];
			st = lo + Mod[-lo, p];

			If[st > hi, Continue[]];
			Do[
				S[[k]] *= -p,
				{k, st - lo + 1, hi - lo + 1, p}
			];

			st = lo + Mod[-lo, p^2];
			If[st > hi, Continue[]];

			Do[
				S[[k]] = 0,
				{k, st - lo + 1, hi - lo + 1, p^2}
			],
			{i, 1, Length[primes]}
		];

		Do[
			If[Abs[S[[k]]] < k + lo - 1, S[[k]] = -Sign[S[[k]]]];
			S[[k]] = Sign[S[[k]]],
			{k, 1, Length[S]}
		];

		If[\[CapitalDelta] == 1,
			S,
			S[[1 ;; -1 ;; \[CapitalDelta]]]
		]
	]
];


(* ::Subsection::Closed:: *)
(*LeastPrimeFactor*)


SegmentedLeastPrimeFactorSieve = fastCompile[{{lo, _Integer}, {hi, _Integer}, {\[CapitalDelta], _Integer}, {primes, _Integer, 1}},
	Module[{S = Range[lo, hi], sqrt = Round[Sqrt[hi]], p, st},
		Do[
			p = primes[[i]];

			st = lo + Mod[-lo, p];

			If[st > hi, Continue[]];
			If[st == p, st += p];
			Do[
				S[[k]] = p,
				{k, st - lo + 1, hi - lo + 1, p}
			],
			{i, Length[primes], 1, -1}
		];

		If[\[CapitalDelta] == 1,
			S,
			S[[1 ;; -1 ;; \[CapitalDelta]]]
		]
	]
];


(* ::Subsection::Closed:: *)
(*SquareFree*)


SegmentedSquareFreeSieve = fastCompile[{{lo, _Integer}, {hi, _Integer}, {\[CapitalDelta], _Integer}, {primes, _Integer, 1}},
	Module[{S = Range[lo, hi], sqrt = Round[Sqrt[hi]], p, st},

		Do[
			p = primes[[i]];

			st = lo + Mod[-lo, p^2];
			If[st > hi, Continue[]];

			Do[
				S[[k]] = 0,
				{k, st - lo + 1, hi - lo + 1, p^2}
			],
			{i, 1, Length[primes]}
		];

		If[\[CapitalDelta] == 1,
			Select[S, Positive],
			Select[S[[1 ;; -1 ;; \[CapitalDelta]]], Positive]
		]
	]
];


(* ::Subsection::Closed:: *)
(*SquareFreeQ*)


SegmentedSquareFreeQSieve = fastCompile[{{lo, _Integer}, {hi, _Integer}, {\[CapitalDelta], _Integer}, {primes, _Integer, 1}},
	Module[{S = Table[1, {hi - lo + 1}], sqrt = Round[Sqrt[hi]], p, st},

		Do[
			p = primes[[i]];

			st = lo + Mod[-lo, p^2];
			If[st > hi, Continue[]];

			Do[
				S[[k]] = 0,
				{k, st - lo + 1, hi - lo + 1, p^2}
			],
			{i, 1, Length[primes]}
		];

		If[\[CapitalDelta] == 1,
			S,
			S[[1 ;; -1 ;; \[CapitalDelta]]]
		]
	]
];


(* ::Subsection::Closed:: *)
(*DivisorSigma*)


(* ::Text:: *)
(*TODO*)


SegmentedDivisorSigmaSieve = fastCompile[{{k, _Integer}, {lo, _Integer}, {hi, _Integer}, {\[CapitalDelta], _Integer}, {primes, _Integer, 1}},
	Module[{S = Table[1, {hi - lo + 1}], sqrt = Round[Sqrt[hi]], p, st, P, LO, HI},

		LO = Range[1, hi-1, hi - lo + 1];
		HI = Append[Rest[LO-1], hi];

		Do[
			P = SegmentedPrimeSieve[LO[[k]], HI[[k]], 1, primes];

			Do[
				p = P[[i]];
				st = lo + Mod[-lo, p];
				If[st > hi, Continue[]];
				S[[st - lo + 1 ;; -1 ;; p]] *= p-1;

				If[p^2 <= hi,
					Do[
						st = lo + Mod[-lo, p^a];
						If[st > hi, Continue[]];
						S[[st - lo + 1 ;; -1 ;; p^a]] *= p,
						{a, 2, Floor[Log[p, hi] + .001]}
					]
				],
				{i, 1, Length[P]}
			],
			{k, 1, Length[LO]}
		];

		If[\[CapitalDelta] == 1,
			S,
			S[[1 ;; -1 ;; \[CapitalDelta]]]
		]
	]
];


(* ::Subsection::Closed:: *)
(*EulerPhi*)


SegmentedEulerPhiSieve = fastCompile[{{lo, _Integer}, {hi, _Integer}, {\[CapitalDelta], _Integer}, {primes, _Integer, 1}},
	Module[{S = Table[1, {hi - lo + 1}], sqrt = Round[Sqrt[hi]], p, st, P, next = 0},

		Do[
			P = SegmentedPrimeSieve[LO, Min[LO + hi - lo, hi], 1, primes];

			Do[
				p = P[[i]];
				st = lo + Mod[-lo, p];
				If[st > hi, Continue[]];

				Do[
					S[[k]] *= p-1,
					{k, st - lo + 1, -1, p}
				];

				next = p^2;
				If[next <= hi,
					Do[
						st = lo + Mod[-lo, next];
						If[st > hi, Continue[]];
						Do[S[[k]] *= p, {k, st - lo + 1, -1, next}];
						next *= p,
						{a, 2, Floor[Log[p, hi] + .001]}
					];
				],
				{i, 1, Length[P]}
			],
			{LO, 1, hi-1, hi - lo + 1}
		];

		If[\[CapitalDelta] == 1,
			S,
			S[[1 ;; -1 ;; \[CapitalDelta]]]
		]
	]
];


(* ::Subsection::Closed:: *)
(*MangoldtLambda*)


SegmentedPrimePowerBaseSieve = fastCompile[{{lo, _Integer}, {hi, _Integer}, {primes, _Integer, 1}},
	Module[{S, P, sqrt = Round[Sqrt[hi]], p, st, next},
		S = Table[-1, {hi - lo + 1}];
		P = Range[lo, hi];
		Do[
			p = primes[[i]];

			If[p > sqrt, Break[]];
			st = Max[lo + Mod[-lo, p], 2p];

			If[st > hi, Continue[]];
			next = p^Max[2, IntegerLength[lo-1, p]];

			Do[
				If[k == next, 
					next *= p;
					P[[k - lo + 1]] = p;
					Continue[]
				];
				S[[k - lo + 1]]++;
				P[[k - lo + 1]] = p,
				{k, st, hi, p}
			],
			{i, 1, Length[primes]}
		];

		If[lo <= 1 <= hi, S[[2 - lo]] = 0];

		P*(1 - UnitStep[S])
	]
];


Clear[SegmentedMangoldtLambdaSieve];


SegmentedMangoldtLambdaSieve = fastCompile[{{lo, _Integer}, {hi, _Integer}, {\[CapitalDelta], _Integer}, {primes, _Integer, 1}},
	Module[{S},
		S = Table[If[p == 0, 0., Log[p]], {p, SegmentedPrimePowerBaseSieve[lo, hi, primes]}];

		If[\[CapitalDelta] == 1,
			S,
			S[[1 ;; -1 ;; \[CapitalDelta]]]
		]
	]
]


(* ::Subsection::Closed:: *)
(*PrimeNu*)


SegmentedPrimeNuSieve = fastCompile[{{lo, _Integer}, {hi, _Integer}, {\[CapitalDelta], _Integer}, {primes, _Integer, 1}},
	Module[{S, P, sqrt = Floor[Sqrt[hi]], next, st},

		S = Table[0, {hi - lo + 1}];
		P = Table[1, {hi - lo + 1}];

		Do[
			If[p > sqrt, Break[]];
			st = lo + Mod[-lo, p];

			If[st > hi, Continue[]];

			Do[
				S[[k]]++;
				P[[k]] *= p,
				{k, st - lo + 1, hi - lo + 1, p}
			];

			next = p^2;
			While[next <= hi,
				st = lo + Mod[-lo, next];
				Do[
					P[[k]] *= p,
					{k, st - lo + 1, hi - lo + 1, next}
				];
				next *= p
			],
			{p, primes}
		];

		Do[
			If[P[[k]] != k + lo - 1, S[[k]]++],
			{k, 1, hi - lo + 1}
		];

		If[\[CapitalDelta] == 1,
			S,
			S[[1 ;; -1 ;; \[CapitalDelta]]]
		]
	]
];


(* ::Subsection::Closed:: *)
(*PrimeOmega*)


SegmentedPrimeOmegaSieve = fastCompile[{{lo, _Integer}, {hi, _Integer}, {\[CapitalDelta], _Integer}, {primes, _Integer, 1}},
	Module[{S, P, sqrt = Floor[Sqrt[hi]], next, st},

		S = Table[0, {hi - lo + 1}];
		P = Table[1, {hi - lo + 1}];

		Do[
			If[p > sqrt, Break[]];

			st = lo + Mod[-lo, p];
			If[st > hi, Continue[]];

			next = p;
			While[next <= hi,
				st = lo + Mod[-lo, next];
				Do[
					S[[k]]++;
					P[[k]] *= p,
					{k, st - lo + 1, hi - lo + 1, next}
				];
				next *= p
			],
			{p, primes}
		];

		Do[
			If[P[[k]] != k + lo - 1, S[[k]]++],
			{k, 1, hi - lo + 1}
		];

		If[\[CapitalDelta] == 1,
			S,
			S[[1 ;; -1 ;; \[CapitalDelta]]]
		]
	]
];


(* ::Subsection::Closed:: *)
(*LiouvilleLambda*)


SegmentedLiouvilleLambdaSieve = fastCompile[{{lo, _Integer}, {hi, _Integer}, {\[CapitalDelta], _Integer}, {primes, _Integer, 1}},
	Module[{S, P, sqrt = Floor[Sqrt[hi]], next, st},

		S = Table[1, {hi - lo + 1}];
		P = Table[1, {hi - lo + 1}];

		Do[
			If[p > sqrt, Break[]];

			st = lo + Mod[-lo, p];
			If[st > hi, Continue[]];

			next = p;
			While[next <= hi,
				st = lo + Mod[-lo, next];
				Do[
					S[[k]] *= -1;
					P[[k]] *= p,
					{k, st - lo + 1, hi - lo + 1, next}
				];
				next *= p
			],
			{p, primes}
		];

		Do[
			If[P[[k]] != k + lo - 1, S[[k]] *= -1],
			{k, 1, hi - lo + 1}
		];

		If[\[CapitalDelta] == 1,
			S,
			S[[1 ;; -1 ;; \[CapitalDelta]]]
		]
	]
];


(* ::Section::Closed:: *)
(*Sieve*)


(* ::Subsection:: *)
(*Sieve and SieveFunction*)


(* ::Subsubsection::Closed:: *)
(*Utilities*)


With[{w = 29},
	icon = Graphics[{Raster[Reverse@Partition[Range[w^2], w] /. {i_Integer?PrimeQ -> {1, .5, .5, 1}, i_Integer -> {1, 1, 1, 0}}]},
		AspectRatio->1,Axes->{False,False},AxesLabel->{None,None},AxesOrigin->{0.,0.},Background->GrayLevel[0.93],BaseStyle->{FontFamily->"Arial"},DisplayFunction->Identity,
		Frame->{{True,True},{True,True}},FrameLabel->{{None,None},{None,None}},FrameStyle->Directive[Thickness[Tiny],GrayLevel[0.7]],FrameTicks->{{None,None},{None,None}},
		GridLines->{None,None},GridLinesStyle->Directive[GrayLevel[0.5,0.4]],ImageSize->{Automatic,Dynamic[3.5*(CurrentValue["FontCapHeight"]/AbsoluteCurrentValue[Magnification])]},
		LabelStyle->{FontFamily->"Arial"},Method->{"ScalingFunctions"->None},PlotRange->{{1,w-1},{1,w-1}},PlotRangeClipping->True,PlotRangePadding->{{1,1},{1,1}},
		Ticks->{Automatic,Automatic}
	]
];


$SieveFunctionList = {
	Prime, PrimesInRange,
	PrimeQ, PrimeQTable,
	PrimePowerQ, PrimePowerQTable,
	MoebiusMu, MoebiusMuTable,
	LeastPrimeFactorsTable,
	SquareFree, SquareFreeInRange,
	SquareFreeQ, SquareFreeQTable,
	EulerPhi, EulerPhiTable,
	MangoldtLambda, MangoldtLambdaTable,
	PrimeNu, PrimeNuTable,
	PrimeOmega, PrimeOmegaTable,
	LiouvilleLambda, LiouvilleLambdaTable
};


SieveFunctionQ[f_] := MemberQ[$SieveFunctionList, f]


CompiledSieveFunction[Prime | PrimesInRange] = SegmentedPrimeSieve;
CompiledSieveFunction[PrimeQ | PrimeQTable] = SegmentedPrimeQSieve;
CompiledSieveFunction[PrimePowerQ | PrimePowerQTable] = SegmentedPrimePowerQSieve;
CompiledSieveFunction[MoebiusMu | MoebiusMuTable] = SegmentedMoebiusMuSieve;
CompiledSieveFunction[LeastPrimeFactorsTable] = SegmentedLeastPrimeFactorSieve;
CompiledSieveFunction[SquareFree | SquareFreeInRange] = SegmentedSquareFreeSieve;
CompiledSieveFunction[SquareFreeQ | SquareFreeQTable] = SegmentedSquareFreeQSieve;
CompiledSieveFunction[EulerPhi | EulerPhiTable] = SegmentedEulerPhiSieve;
CompiledSieveFunction[MangoldtLambda | MangoldtLambdaTable] = SegmentedMangoldtLambdaSieve;
CompiledSieveFunction[PrimeNu | PrimeNuTable] = SegmentedPrimeNuSieve;
CompiledSieveFunction[PrimeOmega | PrimeOmegaTable] = SegmentedPrimeOmegaSieve;
CompiledSieveFunction[LiouvilleLambda | LiouvilleLambdaTable] = SegmentedLiouvilleLambdaSieve;


DataName[PrimeQ | PrimeQTable] = "primality tests";
DataName[PrimePowerQ | PrimePowerQTable] = "prime power tests";
DataName[MoebiusMu | MoebiusMuTable] = "Moebius mu";
DataName[LeastPrimeFactorsTable] = "least prime factors";
DataName[SquareFree | SquareFreeInRange] = "square free integers";
DataName[SquareFreeQ | SquareFreeQTable] = "square free tests";
DataName[EulerPhi | EulerPhiTable] = "Euler totients";
DataName[MangoldtLambda | MangoldtLambdaTable] = "Mangoldt lambda";
DataName[PrimeNu | PrimeNuTable] = "Prime nu";
DataName[PrimeOmega | PrimeOmegaTable] = "Prime omega";
DataName[LiouvilleLambda | LiouvilleLambdaTable] = "Liouville lambda";


(* ::Subsubsection::Closed:: *)
(*Formatting*)


SieveFunction /: MakeBoxes[SieveFunction[max_, primes_], StandardForm] := BoxForm`ArrangeSummaryBox[SieveFunction, f, icon, {
		BoxForm`MakeSummaryItem[{"Domain: ", Row[{1, " to ", sfConciseFormat[max]}]}, StandardForm],
		BoxForm`MakeSummaryItem[{"Number of primes precomputed: ", Length[primes]}, StandardForm]
	},
	{},
	StandardForm
]


SieveFunction /: MakeBoxes[SieveFunction[f_, max_, primes_], StandardForm] := BoxForm`ArrangeSummaryBox[SieveFunction, f, icon, {
		BoxForm`MakeSummaryItem[{"Function: ", ToString[f]}, StandardForm],
		BoxForm`MakeSummaryItem[{"Domain: ", Row[{1, " to ", sfConciseFormat[max]}]}, StandardForm]
	}, {
		BoxForm`MakeSummaryItem[{"Number of primes precomputed: ", Length[primes]}, StandardForm]
	},
	StandardForm
]


SieveFunction /: MakeBoxes[SieveFunction[f_, max_, primes_, data_], StandardForm] := BoxForm`ArrangeSummaryBox[SieveFunction, f, icon, {
		BoxForm`MakeSummaryItem[{"Function: ", ToString[f]}, StandardForm],
		BoxForm`MakeSummaryItem[{"Domain: ", Row[{1, " to ", sfConciseFormat[max]}]}, StandardForm]
	}, {
		BoxForm`MakeSummaryItem[{"Number of " <> DataName[f] <> " precomputed: ", Length[data]}, StandardForm],
		BoxForm`MakeSummaryItem[{"Number of primes precomputed: ", Length[primes]}, StandardForm]
	},
	StandardForm
]


sfConciseFormat[max_] := Block[{lg, dig, offset = 0, logs, res},
	If[IntegerQ[lg = Log2[max]], Return[HoldForm[2^#]&[lg]]];

	dig = IntegerDigits[max];
	If[max >= 10^8 && MatchQ[dig, {_, Longest[0..], z__} /; Length[{z}] < 5],
		offset = FromDigits[Rest[dig]]
	];
	If[max >= 10^8 && MatchQ[dig, {_, Longest[9..], z__} /; Length[{z}] < 5],
		With[{x = FromDigits[Rest[dig]]},
			offset = x - 10^Ceiling[Log10[x]]
		]
	];

	logs = Select[Transpose[{Range[9], Log10[(max - offset)/Range[9]]}], IntegerQ[Last[#]]&];
	Which[
		Length[logs] == 0,
			max,
		res = First[logs];
		First[res] == 1 && offset == 0,
			HoldForm[10^#2]& @@ res,
		First[res] == 1,
			HoldForm[10^# + #2]&[First[res], offset],
		offset == 0,
			HoldForm[#1*10^#2]& @@ res,
		True,
			HoldForm[#1*10^#2 + #3]& @@ Append[res, offset]
	]
]


(* ::Subsubsection::Closed:: *)
(*Main*)


Sieve[max_] := SieveFunction[max, PrimesInRange[Floor[Sqrt[max]]]]


Sieve[PrimesInRange, max_] /; max <= 104729 := SieveFunction[PrimesInRange, max, PrimesInRange[max]]


Sieve[PrimesInRange, max_] := SieveFunction[PrimesInRange, max, PrimesInRange[Floor[Sqrt[max]]]]


Sieve[SquareFreeInRange, max_] /; max <= 16446 := SieveFunction[SquareFreeInRange, max, {}, SquareFreeInRange[max]]


Sieve[f_?SieveFunctionQ, max_] /; max <= 10000 := SieveFunction[f, max, {}, f[max]]


Sieve[f_?SieveFunctionQ, max_] := SieveFunction[f, max, PrimesInRange[Floor[Sqrt[max]]], f[Floor[2CubeRoot[max]]]]


SieveFunction[max_, primes_][f_?SieveFunctionQ][hi_] /; 0 < hi <= max := CompiledSieveFunction[f][1, Floor[hi], 1, primes]

SieveFunction[max_, primes_][f_?SieveFunctionQ][lo_, hi_] /; 0 < lo <= hi <= max := CompiledSieveFunction[f][Ceiling[lo], Floor[hi], 1, primes]

SieveFunction[max_, primes_][f_?SieveFunctionQ][lo_, hi_, \[CapitalDelta]_Integer] /; 0 < lo <= hi <= max && \[CapitalDelta] > 0 := CompiledSieveFunction[f][Ceiling[lo], Floor[hi], \[CapitalDelta], primes]


SieveFunction[Prime|PrimesInRange, max_, primes_][hi_] /; 0 < hi <= Last[primes] := primes[[1 ;; PrimePi[hi]]]

SieveFunction[Prime|PrimesInRange, max_, primes_][lo_, hi_] /; 0 < lo <= hi <= Last[primes] := primes[[PrimePi[lo-1] + 1 ;; PrimePi[hi]]]

SieveFunction[Prime|PrimesInRange, max_, primes_][lo_, hi_, \[CapitalDelta]_Integer] /; 0 < lo <= hi <= Last[primes] && \[CapitalDelta] > 0 := primes[[PrimePi[lo-1] + 1 ;; PrimePi[hi] ;; \[CapitalDelta]]]


SieveFunction[f_?SieveFunctionQ, max_, primes_][hi_] /; 0 < hi <= max := CompiledSieveFunction[f][1, Floor[hi], 1, primes]

SieveFunction[f_?SieveFunctionQ, max_, primes_][lo_, hi_] /; 0 < lo <= hi <= max := CompiledSieveFunction[f][Ceiling[lo], Floor[hi], 1, primes]

SieveFunction[f_?SieveFunctionQ, max_, primes_][lo_, hi_, \[CapitalDelta]_Integer] /; 0 < lo <= hi <= max && \[CapitalDelta] > 0 := CompiledSieveFunction[f][Ceiling[lo], Floor[hi], \[CapitalDelta], primes]


SieveFunction[f_?SieveFunctionQ, max_, primes_, data_][hi_] /; 0 < hi <= Length[data] := data[[1 ;; Floor[hi]]]

SieveFunction[f_?SieveFunctionQ, max_, primes_, data_][lo_, hi_] /; 0 < lo <= hi <= Length[data] := data[[Ceiling[lo] ;; Floor[hi]]]

SieveFunction[f_?SieveFunctionQ, max_, primes_, data_][lo_, hi_, \[CapitalDelta]_Integer] /; 0 < lo <= hi <= Length[data] && \[CapitalDelta] > 0 := data[[Ceiling[lo] ;; Floor[hi] ;; \[CapitalDelta]]]


SieveFunction[f_?SieveFunctionQ, max_, primes_, _][hi_] /; 0 < hi <= max := CompiledSieveFunction[f][1, Floor[hi], 1, primes]

SieveFunction[f_?SieveFunctionQ, max_, primes_, _][lo_, hi_] /; 0 < lo < hi <= max := CompiledSieveFunction[f][Ceiling[lo], Floor[hi], 1, primes]

SieveFunction[f_?SieveFunctionQ, max_, primes_, _][lo_, hi_, \[CapitalDelta]_Integer] /; 0 < lo < hi <= max && \[CapitalDelta] > 0 := CompiledSieveFunction[f][Ceiling[lo], Floor[hi], \[CapitalDelta], primes]


(* ::Section::Closed:: *)
(*Arithmetic functions over a range*)


(* ::Text:: *)
(*TODO: add integer factoring... but Compile can't handle ragged lists...*)


(* ::Subsection::Closed:: *)
(*PrimesInRange*)


PrimesInRange[hi_] := PrimesInRangeCompiled[hi]


PrimesInRange[lo_, hi_] := PrimesInRange[lo, hi, 1]
PrimesInRange[lo_, hi_, \[CapitalDelta]_] := SegmentedPrimeSieve[lo, hi, \[CapitalDelta], PrimesInRangeCompiled[Floor[Sqrt[hi]]]]


PrimesInRangeCompiled = fastCompile[{{n, _Integer}},
	Block[{S = Range[2, n]},
		Do[
			If[S[[i]] != 0,
				Do[
					S[[k]] = 0,
					{k, 2i+1, n-1, i+1}
				]
			],
			{i, Sqrt[n]}
		];
		Select[S, Positive]
	]
];


(* ::Subsection::Closed:: *)
(*PrimeTable*)


PrimeTable[hi_] := PrimeTable[1, hi, 1]


PrimeTable[lo_, hi_] := PrimeTable[lo, hi, 1]
PrimeTable[lo_, hi_, \[CapitalDelta]_] := PrimesInRange[Prime[lo], Prime[hi], \[CapitalDelta]]


(* ::Subsection::Closed:: *)
(*PrimeQTable*)


PrimeQTable[hi_] := PrimeQTableCompiled[hi]


PrimeQTable[lo_, hi_] := PrimeQTable[lo, hi, 1]
PrimeQTable[lo_, hi_, \[CapitalDelta]_] := SegmentedPrimeQSieve[lo, hi, \[CapitalDelta], PrimesInRangeCompiled[Floor[Sqrt[hi]]]]


PrimeQTableCompiled = fastCompile[{{n, _Integer}},
	Block[{S = Table[1, {n}]},
		S[[1]] = 0;
		Do[
			If[S[[i]] != 0,
				Do[
					S[[k]] = 0,
					{k, 2i, n, i}
				]
			],
			{i, Sqrt[n]}
		];
		S
	]
];


(* ::Subsection::Closed:: *)
(*PrimePowerQTable*)


PrimePowerQTable[hi_] := PrimePowerQTableCompiled[hi]


PrimePowerQTable[lo_, hi_] := PrimePowerQTable[lo, hi, 1]
PrimePowerQTable[lo_, hi_, \[CapitalDelta]_] := SegmentedPrimePowerQSieve[lo, hi, \[CapitalDelta], PrimesInRangeCompiled[Floor[Sqrt[hi]]]]


PrimePowerQTableCompiled = fastCompile[{{n, _Integer}},
	Module[{primes, S, sqrt = Round[Sqrt[n]], p, st, next},
		primes = PrimesInRangeCompiled[sqrt];
		S = Table[-1, {n}];

		Do[
			p = primes[[i]];

			If[p > sqrt, Break[]];
			st = 2p;

			If[st > n, Continue[]];
			next = p^2;
			Do[
				If[k == next, 
					next *= p;
					Continue[]
				];
				S[[k]]++,
				{k, st, n, p}
			],
			{i, 1, Length[primes]}
		];

		S[[1]] = 0;
		1 - UnitStep[S]
	]
];


(* ::Subsection::Closed:: *)
(*MoebiusMuTable*)


MoebiusMuTable[hi_] := MoebiusMuTableCompiled[hi]


MoebiusMuTable[lo_, hi_] := MoebiusMuTable[lo, hi, 1]
MoebiusMuTable[lo_, hi_, \[CapitalDelta]_] := SegmentedMoebiusMuSieve[lo, hi, \[CapitalDelta], PrimesInRangeCompiled[Floor[Sqrt[hi]]]]


MoebiusMuTableCompiled = fastCompile[{{n, _Integer}},
	Module[{S = Table[1, {n}], primes, p, st},
		primes = PrimesInRangeCompiled[Floor[Sqrt[n]]];

		Do[
			p = primes[[i]];
			st = 1 + Mod[-1, p];
			If[st > n, Continue[]];

			Do[
				S[[k]] *= -p,
				{k, st, n, p}
			];

			st = 1 + Mod[-1, p^2];
			If[st > n, Continue[]];

			Do[
				S[[k]] = 0,
				{k, st, n, p^2}
			],
			{i, 1, Length[primes]}
		];

		Do[
			If[Abs[S[[k]]] < k, S[[k]] *= -1];
			S[[k]] = Sign[S[[k]]];,
			{k, 1, Length[S]}
		];

		S
	]
];


(* ::Subsection::Closed:: *)
(*LeastPrimeFactorsTable*)


LeastPrimeFactor[n_Integer] := With[{facs = FactorInteger[n]},
	(If[facs[[1, 1]] < 0, Rest, Identity][facs])[[1, 1]]
]


LeastPrimeFactorsTable[hi_] := LeastPrimeFactorsTableCompiled[hi]


LeastPrimeFactorsTable[lo_, hi_] := LeastPrimeFactorsTable[lo, hi, 1]
LeastPrimeFactorsTable[lo_, hi_, \[CapitalDelta]_] := SegmentedLeastPrimeFactorSieve[lo, hi, \[CapitalDelta], PrimesInRangeCompiled[Floor[Sqrt[hi]]]]


LeastPrimeFactorsTableCompiled = fastCompile[{{n, _Integer}},
	Module[{S = Range[n], primes, p, st},
		primes = PrimesInRangeCompiled[Floor[Sqrt[n]]];

		Do[
			p = primes[[i]];

			st = 1 + Mod[-1, p];

			If[st > n, Continue[]];
			If[st == p, st += p];
			Do[
				S[[k]] = p,
				{k, st, n, p}
			],
			{i, Length[primes], 1, -1}
		];

		S
	]
];


(* ::Subsection::Closed:: *)
(*SquareFreeInRange*)


SquareFreeInRange[hi_] := SquareFreeInRangeCompiled[hi]


SquareFreeInRange[lo_, hi_] := SquareFreeInRange[lo, hi, 1]
SquareFreeInRange[lo_, hi_, \[CapitalDelta]_] := SegmentedSquareFreeSieve[lo, hi, \[CapitalDelta], PrimesInRangeCompiled[Floor[Sqrt[hi]]]]


SquareFreeInRangeCompiled = fastCompile[{{n, _Integer}},
	Module[{S = Range[n], primes, p, st},
		primes = PrimesInRangeCompiled[Floor[Sqrt[n]]];

		Do[
			p = primes[[i]];

			st = p^2;
			If[st > n, Continue[]];

			Do[
				S[[k]] = 0,
				{k, st, n, st}
			],
			{i, 1, Length[primes]}
		];

		Select[S, Positive]
	]
];


(* ::Subsection::Closed:: *)
(*SquareFreeQTable*)


SquareFreeQTable[hi_] := SquareFreeQTableCompiled[hi]


SquareFreeQTable[lo_, hi_] := SquareFreeQTable[lo, hi, 1]
SquareFreeQTable[lo_, hi_, \[CapitalDelta]_] := SegmentedSquareFreeQSieve[lo, hi, \[CapitalDelta], PrimesInRangeCompiled[Floor[Sqrt[hi]]]]


SquareFreeQTableCompiled = fastCompile[{{n, _Integer}},
	Module[{S = Table[1, {n}], primes, p, st},
		primes = PrimesInRangeCompiled[Floor[Sqrt[n]]];

		Do[
			p = primes[[i]];

			st = p^2;
			If[st > n, Continue[]];

			Do[
				S[[k]] = 0,
				{k, st, n, st}
			],
			{i, 1, Length[primes]}
		];

		S
	]
];


(* ::Subsection::Closed:: *)
(*DivisorSigmaTable*)


DivisorSigmaTable[k_, hi_] := DivisorSigmaTableCompiled[k, hi]


DivisorSigmaTableCompiled = fastCompile[{{k, _Integer}, {n, _Integer}},
	Block[{primes, divs = Table[1, {n}], p = 0, q = 0},
		primes = LeastPrimeFactorsTableCompiled[n];
		Do[
			p = primes[[i]];
			q = Quotient[i, p];
			If[Mod[q, p] != 0,
				divs[[i]] = (p^k + 1)divs[[q]],
				divs[[i]] = (p^k + 1)divs[[q]] - p^k divs[[Quotient[q, p]]]
			],
			{i, 2, n}
		];
		divs
	]
];


(* ::Subsection::Closed:: *)
(*EulerPhiTable*)


EulerPhiTable[hi_] := EulerPhiTableCompiled[hi]


EulerPhiTableCompiled = fastCompile[{{n, _Integer}},
	Block[{primes, phis = Table[1, {n}], p = 0, q = 0},
		primes = LeastPrimeFactorsTableCompiled[n];
		Do[
			p = primes[[i]];
			q = Quotient[i, p];
			If[Mod[q, p] != 0,
				phis[[i]] = (p-1)phis[[q]],
				phis[[i]] = p phis[[q]]
			],
			{i, 2, n}
		];
		phis
	]
];


(* ::Subsection::Closed:: *)
(*MangoldtLambdaTable*)


MangoldtLambdaTable[hi_] := MangoldtLambdaTable[1, hi, 1]
MangoldtLambdaTable[lo_, hi_] := MangoldtLambdaTable[lo, hi, 1]


MangoldtLambdaTable[lo_, hi_, \[CapitalDelta]_] := SegmentedMangoldtLambdaSieve[lo, hi, \[CapitalDelta], PrimesInRangeCompiled[Floor[Sqrt[hi]]]]


(* ::Subsection::Closed:: *)
(*PrimeNuTable*)


PrimeNuTable[hi_] := PrimeNuTableCompiled[hi]


PrimeNuTable[lo_, hi_] := PrimeNuTable[lo, hi, 1]
PrimeNuTable[lo_, hi_, \[CapitalDelta]_] := SegmentedPrimeNuSieve[lo, hi, \[CapitalDelta], PrimesInRangeCompiled[Floor[Sqrt[hi]]]]


PrimeNuTableCompiled = fastCompile[{{n, _Integer}},
	Module[{S = Table[0, {n}], P = Table[1, {n}], sqrt = Floor[Sqrt[n]], primes, next},
		primes = PrimesInRangeCompiled[sqrt];

		Do[
			Do[
				S[[k]]++;
				P[[k]] *= p,
				{k, p, n, p}
			];

			next = p^2;
			While[next <= n,
				Do[
					P[[k]] *= p,
					{k, next, n, next}
				];
				next *= p
			],
			{p, primes}
		];

		Do[
			If[P[[k]] != k, S[[k]]++],
			{k, sqrt+1, n}
		];

		S
	]
];


(* ::Subsection::Closed:: *)
(*PrimeOmegaTable*)


PrimeOmegaTable[hi_] := PrimeOmegaTableCompiled[hi]


PrimeOmegaTable[lo_, hi_] := PrimeOmegaTable[lo, hi, 1]
PrimeOmegaTable[lo_, hi_, \[CapitalDelta]_] := SegmentedPrimeOmegaSieve[lo, hi, \[CapitalDelta], PrimesInRangeCompiled[Floor[Sqrt[hi]]]]


PrimeOmegaTableCompiled = fastCompile[{{n, _Integer}},
	Module[{S = Table[0, {n}], P = Table[1, {n}], sqrt = Floor[Sqrt[n]], primes, next},
		primes = PrimesInRangeCompiled[sqrt];

		Do[
			next = p;
			While[next <= n,
				Do[
					S[[k]]++;
					P[[k]] *= p,
					{k, next, n, next}
				];
				next *= p
			],
			{p, primes}
		];

		Do[
			If[P[[k]] != k, S[[k]]++],
			{k, sqrt+1, n}
		];

		S
	]
];


(* ::Subsection::Closed:: *)
(*LiouvilleLambdaTable*)


LiouvilleLambdaTable[hi_] := LiouvilleLambdaTableCompiled[hi]


LiouvilleLambdaTable[lo_, hi_] := LiouvilleLambdaTable[lo, hi, 1]
LiouvilleLambdaTable[lo_, hi_, \[CapitalDelta]_] := SegmentedLiouvilleLambdaSieve[lo, hi, \[CapitalDelta], PrimesInRangeCompiled[Floor[Sqrt[hi]]]]


LiouvilleLambdaTableCompiled = fastCompile[{{n, _Integer}},
	Module[{S = Table[1, {n}], P = Table[1, {n}], sqrt = Floor[Sqrt[n]], primes, next},
		primes = PrimesInRangeCompiled[sqrt];

		Do[
			next = p;
			While[next <= n,
				Do[
					S[[k]] *= -1;
					P[[k]] *= p,
					{k, next, n, next}
				];
				next *= p
			],
			{p, primes}
		];

		Do[
			If[P[[k]] != k, S[[k]] *= -1],
			{k, sqrt+1, n}
		];

		S
	]
];


(* ::Section::Closed:: *)
(*Misc.*)


(* ::Subsection::Closed:: *)
(*SquareFree*)


SquareFreeRangeLowSpace = fastCompile[{{lo, _Integer}, {hi, _Integer}},
	Module[{S = Range[lo, hi], sqrt = Round[Sqrt[hi]], x14, P, L1, L2, primes, p, st},

		x14 = Floor[sqrt];
		P = PrimesInRangeCompiled[x14];
		L1 = L2 = 1;

		While[L2 < sqrt,
			L2 = Min[L1 + x14, sqrt];
			primes = SegmentedPrimeSieve[L1, L2, 1, P];

			Do[
				p = primes[[i]];

				st = lo + Mod[-lo, p^2];
				If[st > hi, Continue[]];

				Do[
					S[[k]] = 0,
					{k, st - lo + 1, hi - lo + 1, p^2}
				],
				{i, 1, Length[primes]}
			];

			L1 = L2 + 1
		];

		Select[S, Positive]
	]
];


SquareFreeIterateUp = fastCompile[{{mid, _Integer}, {pi, _Integer}, {x, _Integer}},
	Module[{L1 = mid, L2, x14 = 10Floor[x^(1/4)], newpi = pi, oldpi = 0, squarefrees = {0}},

		While[True,
			L2 = L1 + x14;

			squarefrees = SquareFreeRangeLowSpace[L1, L2];
			oldpi = newpi;
			newpi += Length[squarefrees];

			If[newpi >= x, Break[]];

			L1 = L2 + 1
		];

		squarefrees[[x - oldpi]]
	]
];


SquareFreeIterateDown = fastCompile[{{mid, _Integer}, {pi, _Integer}, {x, _Integer}},
	Module[{L1, L2 = mid, x14 = 10Floor[x^(1/4)], newpi = pi, oldpi = 0, squarefrees = {0}},

		While[True,
			L1 = L2 - x14;

			squarefrees = SquareFreeRangeLowSpace[L1, L2];
			oldpi = newpi;
			newpi -= Length[squarefrees];

			If[newpi <= x, Break[]];

			L2 = L1 - 1
		];

		squarefrees[[x - oldpi - 1]]
	]
];


SquareFree = fastCompile[{{x, _Integer}},
	Module[{mid = Floor[Pi^2*x/6], pi},
		pi = SquareFreePi[mid];

		If[pi >= x,
			SquareFreeIterateDown[mid, pi, x],
			SquareFreeIterateUp[mid, pi, x]
		]
	]
];


(* ::Input:: *)
(*SquareFreePi[10^12]//AbsoluteTiming*)


(* ::Input:: *)
(*SquareFree[10^12]//AbsoluteTiming*)


(* ::Subsection::Closed:: *)
(*MeisselMerten*)


SetAttributes[MeisselMerten, {Constant}];


MeisselMerten /: MakeBoxes[MeisselMerten, TraditionalForm] := TagBox[TooltipBox[SubscriptBox["B","1"], "MeisselMerten", LabelStyle -> "TextStyling"], \!\(\*
TagBox["#1",
Annotation[#, "MeisselMerten", "Tooltip"]& ]\)&]


N[MeisselMerten] ^= NMeisselMerten[MachinePrecision];


MeisselMerten /: N[MeisselMerten, {p_, _}] := NMeisselMerten[p]


MeisselMerten /: N[MeisselMerten, p_] := NMeisselMerten[p]


NMeisselMerten[MachinePrecision] = 0.26149721284764277`;


NMeisselMerten[p_] := Block[{\[Mu], ss, pr, psum, tmp, prev = 0, n = 1, wp = p + 15},
	\[Mu] = MoebiusMuTableCompiled[Max[Ceiling[p], 30]];
	ss = N[1, wp];
	pr = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53}^-ss;
	prev = Total[pr];
	psum = prev + EulerGamma + Log[Times @@ (1-pr)];
	While[psum-prev!=0,
		While[(tmp = \[Mu][[++n]]) == 0, Null];
		prev = psum;
		psum += tmp/n Log[Zeta[n ss] Times @@ (1-pr^n)]
	];
	NumericalMath`LowerPrecision[psum, p]
]


(* ::Section::Closed:: *)
(*Summatory functions*)


(* ::Subsection::Closed:: *)
(*SquareFreePi*)


SquareFreePi = fastCompile[{{x, _Integer}},
	Block[{u, sqrt = Floor[Sqrt[x - 1] + 0.000001], B, primes, sum = 0, L1 = 1, L2 = 1},
		B = Ceiling[10x^(1/4)];
		primes = PrimesInRangeCompiled[Ceiling[Sqrt[sqrt]]];

		While[L2 < sqrt,
			L2 = Min[L1 + B, sqrt];
			sum += SegmentedMoebiusMuSieve[L1, L2, 1, primes].Quotient[x, Range[L1, L2]^2];
			L1 = L2 + 1
		];

		sum
	]
];


(* ::Subsection::Closed:: *)
(*MertenM*)


MertenM /: MakeBoxes[MertenM[x_], TraditionalForm] := With[{mx = MakeBoxes[x, TraditionalForm]},
	TagBox[TooltipBox[RowBox[{"M", "(", mx, ")"}], "MertenM", LabelStyle -> "TextStyling"], \!\(\*
TagBox["#1",
Annotation[#, "MertenM", "Tooltip"]& ]\)&]
]


lcount = fastCompile[{{y, _Integer}, {k, _Integer}},
	If[y < (k+1)^2,
		Quotient[y, k] - Floor[Sqrt[y] + .000001],
		Quotient[y, k] - Quotient[y, k+1]
	]
];


accumulate = fastCompile[{{lis, _Integer, 1}},
	Module[{acc = Table[0, {Length[lis]}]},
		acc[[1]] = lis[[1]];
		Do[
			acc[[i]] = acc[[i-1]] + lis[[i]],
			{i, 2, Length[lis]}
		];
		acc
	]
];


MertenM = fastCompile[{{x, _Integer}},
	Block[{u, sqrt = Floor[Sqrt[x] + .000001], B, CAP, primes, \[Mu], Mold = 0, M, Mu, L1, L2 = 0, S1 = 0, S2 = 0},
		u = Ceiling[(1/3)*x^(1/3)Log[Log[x]]^(2/3)];
		B = 10u;
		CAP = Ceiling[x/u];
		primes = PrimesInRangeCompiled[Ceiling[Sqrt[CAP]]];
		\[Mu] = SegmentedMoebiusMuSieve[1, u, 1, primes];
		Mu = Total[\[Mu]];

		L1 = 0;
		While[L2 < sqrt,
			L2 = Min[L1 + B, sqrt];
			M = Mold + accumulate[SegmentedMoebiusMuSieve[L1, L2, 1, primes]];
			Mold = M[[-2]];
			S1 += Sum[\[Mu][[m]]M[[Quotient[x, m n] - L1 + 1]], {m, Max[1, Quotient[x, L2^2]], u}, {n, Max[Quotient[u, m]+1, Ceiling[x/(m L2)]], Min[If[L1 == 0, x, Ceiling[x/(m L1)-1]], Floor[Sqrt[x/m]]]}];
			S2 += Sum[M[[k - L1 + 1]]\[Mu][[m]]lcount[Quotient[x, m], k], {k, L1+1, L2}, {m, Min[u, Quotient[x, k^2]]}];
			L1 = L2
		];

		While[L2 < CAP,
			L2 = Min[L1 + B, CAP];
			M = Mold + accumulate[SegmentedMoebiusMuSieve[L1, L2, 1, primes]];
			Mold = M[[-2]];
			S1 += Sum[\[Mu][[m]]M[[Quotient[x, m n] - L1 + 1]], {m, 1, u}, {n, Max[Quotient[u, m]+1, Ceiling[x/(m L2)]], Min[Ceiling[x/(m L1)-1], Floor[Sqrt[x/m]]]}];
			L1 = L2
		];

		Mu - S1 - S2
	]
];


(* ::Subsection::Closed:: *)
(*DivisorSigmaSum*)


(* ::Text:: *)
(*TODO. Dirichlet's hyperbola method will give us a O(Sqrt[x]) runtime.*)


(* ::Subsection::Closed:: *)
(*ChebyshevPsi*)


(* ::Subsubsection::Closed:: *)
(*Compiled... major rounding errors, but fast*)


accumulateReal = fastCompile[{{lis, _Real, 1}},
	Module[{acc = Table[0., {Length[lis]}]},
		acc[[1]] = lis[[1]];
		Do[
			acc[[i]] = acc[[i-1]] + lis[[i]],
			{i, 2, Length[lis]}
		];
		acc
	]
];


(* we assume k \[GreaterEqual] u *)
\[ScriptCapitalN] = fastCompile[{{x, _Integer}, {u, _Integer}, {l, _Integer}, {k, _Integer}, {sqrtxl, _Integer}},
	Module[{qk1 = Quotient[x, l*(k+1)], qk = Quotient[x, l*k], qu = Quotient[x, l*u]},
		If[qu < qk1 + 1 || qk < sqrtxl + 1,
			0,
			Max[0, Min[qu, qk] - Max[sqrtxl, qk1]]
		]
	]
];


(* ::Text:: *)
(*NOTE: since compile can only perform machine precision arithmetic, error occurs. Around 10^12 and up, the absolute error is > 0.1*)


ChebyshevPsi = fastCompile[{{x, _Integer}},
	Module[{u, primes, \[Mu], ppQ, \[CapitalLambda], \[Psi] = {0.}, \[Psi]u, S1, S2, S3, S4a, S4b, o, L1, L2, sqrt, CAP, sqrtCAP, sqrtxl},
		u = If[x < 50,
			x,
			Floor[10x^(1/3)]
		];

		CAP = Ceiling[x/u];
		sqrtCAP = Max[Floor[Sqrt[u]], Floor[Sqrt[CAP]]];
		sqrt = Floor[Sqrt[x]];

		primes = PrimesInRangeCompiled[sqrtCAP];

		\[Mu] = SegmentedMoebiusMuSieve[1, u, 1, primes];

		ppQ = SegmentedPrimePowerBaseSieve[1, u, primes];
		\[CapitalLambda] = Table[If[ppQ[[i]] == 0, 0., Log[ppQ[[i]]]], {i, u}];

		S1 = Total[\[CapitalLambda]];
		S2 = \[Mu].LogGamma[Quotient[x, Range[u]] + 1.];

		(*S3 = Sum[\[Mu][[l]]\[CapitalLambda][[m]]Quotient[x, l*m], {l, u}, {m, u}];*)
		With[{quo = Quotient[x, Range[u]]}, 
			S3 = \[CapitalLambda] . Table[\[Mu] . Quotient[quo, l], {l, u}]
		];

		L1 = L2 = 1;
		S4a = 0.;
		S4b = 0.;
		\[Psi]u = S1;

		While[L2 < sqrt,
			L2 = Min[L1 + u, sqrt];

			ppQ = SegmentedPrimePowerBaseSieve[L1, L2, primes];
			\[Psi] = Last[\[Psi]] + accumulateReal[Table[If[ppQ[[i - L1 + 1]] == 0, 0., Log[ppQ[[i - L1 + 1]]]], {i, L1, L2}]];

			Do[
				sqrtxl = Floor[Sqrt[x/l]];
				S4a += \[Mu][[l]]Sum[\[ScriptCapitalN][x, u, l, k, sqrtxl](\[Psi][[k - L1 + 1]] - \[Psi]u), {k, Max[u, L1], Min[sqrtxl, L2]}],
				{l, u}
			];

			Do[
				S4b += \[Mu][[l]]Sum[\[Psi][[Quotient[x, l*m] - L1 + 1]] - \[Psi]u, {m, Max[Quotient[u, l], Quotient[x, l*(L2+1)]] + 1, Min[Quotient[x, l*u], Floor[Sqrt[x/l]], Quotient[x, l*L1]]}],
				{l, Max[Quotient[x, (L2+1)^2], 1], u}
			];

			L1 = L2 + 1;
		];

		While[L2 < CAP,
			L2 = Min[L1 + u, CAP];

			ppQ = SegmentedPrimePowerBaseSieve[L1, L2, primes];
			\[Psi] = Last[\[Psi]] + accumulateReal[Table[If[ppQ[[i - L1 + 1]] == 0, 0., Log[ppQ[[i - L1 + 1]]]], {i, L1, L2}]];

			Do[
				S4b += \[Mu][[l]]Sum[\[Psi][[Quotient[x, l*m] - L1 + 1]] - \[Psi]u, {m, Max[Quotient[u, l], Quotient[x, l*(L2+1)]] + 1, Min[Quotient[x, l*u], Floor[Sqrt[x/l]], Quotient[x, l*L1]]}],
				{l, u}
			];

			L1 = L2 + 1;
		];

		S1 + S2 - S3 - S4a - S4b
	]
];


(* ::Input:: *)
(*ChebyshevPsi[10^7]//AbsoluteTiming*)


(* ::Input:: *)
(*ChebyshevPsi[10^10]//AbsoluteTiming*)


(* ::Input:: *)
(*(* {{0.01595399999999999943178785599684488261`4.223469500994835,999586.5974956325},{0.0728449999999999930899718947330256924`4.882999660917116,9.998539403346092*^6},{0.49215500000000000913047415451728738844`5.71270181491556,9.999824279662687*^7},{1.81671200000000010454925813974114134908`6.279885998141669,1.0000015959904679*^9},{8.66016199999999969350028550252318382263`6.958125929436465,1.0000042119832893*^10},{34.70681600000000344152795150876045227051`7.561014686644003,1.0000005845642331*^11},{159.70876200000000721956894267350435256958`8.22392865649303,1.0000000401366755*^12},{743.52630099999998947168933227658271789551`8.891896248850633,1.0000000171994219*^13},{3452.57441800000015064142644405364990234375`9.558742961566772,1.0000000061864244*^14},{16068.22938099999919359106570482254028320312`10.226567936127129,9.99999997477054*^14}} *)*)
(*Table[Echo[{#1,InputForm[#2]}&@@AbsoluteTiming[ChebyshevPsi[10^n]]],{n,6,15}]*)


(* ::Subsubsection::Closed:: *)
(*Uncompiled... no rounding errors, but slow*)


ChebyshevPsiSlow[x_] /; Element[x, Reals] && x < 2 = 0;


(* ::Input:: *)
(*ChebyshevPsiSlow[y_] /; y < 10^6 := Module[{x = Floor[y], p, sum = 0, i = 1, ppQ},*)
(*	p = 2If[ExactNumberQ[y], MachinePrecision, Precision[y]];*)
(**)
(*	While[x >= 2,*)
(*		x = Floor[y^(1/i++)];*)
(*		sum += N[Total @ Log @ Pick[Range[x], PrimeQTable[x], 1], p]*)
(*	];*)
(**)
(*	N[sum, p]*)
(*];*)


(* ::Text:: *)
(*TODO make less procedural...*)


ChebyshevPsiSlow[y_?Positive] := Module[{u, x = Floor[y], primes, \[Mu], ppQ, \[CapitalLambda], \[Psi], \[Psi]u, S1, S2, S3, S4a, S4b, o, L1, L2, sqrt, CAP, sqrtCAP, sqrtxl, mn, mx, p},
	p = 2If[ExactNumberQ[y], MachinePrecision, Precision[y]];

	u = If[x < 50,
		x,
		Floor[10x^(1/3)]
	];

	CAP = Ceiling[x/u];
	sqrtCAP = Max[Floor[Sqrt[u]], Floor[Sqrt[CAP]]];
	sqrt = Floor[Sqrt[x]];

	primes = PrimesInRangeCompiled[sqrtCAP];

	\[Mu] = SegmentedMoebiusMuSieve[1, u, 1, primes];

	ppQ = N[SegmentedPrimePowerBaseSieve[1, u, primes], p];
	\[CapitalLambda] = log /@ ppQ;

	S1 = Total[\[CapitalLambda]];
	S2 = \[Mu].LogGamma[Quotient[x, Range[u]] + N[1, p]];
	With[{quo = Quotient[x, Range[u]]}, 
		S3 = \[CapitalLambda] . Table[\[Mu] . Quotient[quo, l], {l, u}]
	];

	L1 = L2 = 1;
	S4a = N[0, p];
	S4b = N[0, p];
	\[Psi]u = S1;
	\[Psi] = N[{0}, p];

	While[L2 < sqrt,
		L2 = Min[L1 + u, sqrt];

		ppQ = N[SegmentedPrimePowerBaseSieve[L1, L2, primes], p];
		\[Psi] = Last[\[Psi]] + Accumulate[log /@ ppQ];

		S4a += \[Mu] . Table[
			sqrtxl = Floor[Sqrt[x/l]];
			{mn, mx} = {Max[u, L1], Min[sqrtxl, L2]};
			If[mn <= mx,
				Table[\[ScriptCapitalN][x, u, l, k, sqrtxl], {k, mn, mx}] . (\[Psi][[mn - L1 + 1 ;; mx - L1 + 1]] - \[Psi]u),
				0
			],
			{l, u}
		];

		S4b += \[Mu][[Max[Quotient[x, (L2+1)^2], 1] ;; u]] . Table[
			{mn, mx} = {Max[Quotient[u, l], Quotient[x, l*(L2+1)]] + 1, Min[Quotient[x, l*u], Floor[Sqrt[x/l]], Quotient[x, l*L1]]};
			If[mn <= mx,
				Total[\[Psi][[Quotient[x, l*Range[mn, mx]] - L1 + 1]]] - (mx-mn+1)\[Psi]u,
				0
			],
			{l, Max[Quotient[x, (L2+1)^2], 1], u}
		];

		L1 = L2 + 1;
	];

	While[L2 < CAP,
		L2 = Min[L1 + u, CAP];

		ppQ = N[SegmentedPrimePowerBaseSieve[L1, L2, primes], p];
		\[Psi] = Last[\[Psi]] + Accumulate[log /@ ppQ];

		S4b += \[Mu] . Table[
			{mn, mx} = {Max[Quotient[u, l], Quotient[x, l*(L2+1)]] + 1, Min[Quotient[x, l*u], Floor[Sqrt[x/l]], Quotient[x, l*L1]]};
			If[mn <= mx,
				Total[\[Psi][[Quotient[x, l*Range[mn, mx]] - L1 + 1]]] - (mx-mn+1)\[Psi]u,
				0
			],
			{l, u}
		];

		L1 = L2 + 1;
	];

	If[p == 2MachinePrecision, 
		p = Sequence[], 
		p = p/2
	];

	N[S1 + S2 - S3 - S4a - S4b, p]
];


log = Log[# + Boole[# == 0]]&;


(* ::Subsubsection::Closed:: *)
(*Timings*)


(* ::Input:: *)
(*(**)
(*{{0.0116`,1005.064574045967},*)
(*{0.0257`,10157.248645377133},*)
(*{0.0679`,100065.84131801335},*)
(*{0.1274`,999586.597495633},*)
(*{0.653`,9.998539403345976*^6},*)
(*{2.6062`,9.999824279662678*^7},*)
(*{12.3019`,1.0000015959904276*^9},*)
(*{50.2068`,1.0000042119833473*^10},*)
(*{216.35`,1.000000584564303*^11},*)
(*{973.8158`,1.0000000401367655*^12}}*)
(**)*)
(*Table[{Round[#1,10^-4.],InputForm[#2]}&@@AbsoluteTiming[ChebyshevPsiSlow[10^i]],{i,3,12}]*)


(* ::Text:: *)
(*Approximate runtimes based on timings of the uncompiled version: 0.00002266630074202146` x^0.6353158858141099`*)


(* ::Text:: *)
(*Projected timings in seconds:*)


(* ::Input:: *)
(*Table[HoldForm[10^#]&[x]->Floor[0.00002266630074202146`(10^x)^0.6353158858141099`],{x,Range[13,20]}]*)


(* ::Input:: *)
(*(**)
(*{{0.0003`,1005.0645740459674},*)
(*{0.0006`,10157.248645377109},*)
(*{0.0023`,100065.84131801357},*)
(*{0.0103`,999586.5974956302},*)
(*{0.0483`,9.998539403346017*^6},*)
(*{0.2361`,9.999824279662608*^7},*)
(*{1.0862`,1.0000015959904407*^9},*)
(*{5.0784`,1.0000042119833344*^10},*)
(*{23.3816`,1.0000005845641968*^11},*)
(*{108.4132`,1.0000000401367349*^12}}*)
(**)*)
(*Table[{Round[#1,10^-4.],InputForm[#2]}&@@AbsoluteTiming[ChebyshevPsi[10^i]],{i,3,12}]*)


(* ::Text:: *)
(*Compiled version is ~10 times faster but inaccurate :( *)


(* ::Text:: *)
(*Approximate runtimes based on timings of the uncompiled version: 1.0186795297679153`*^-6 x^0.669307362337562`*)


(* ::Text:: *)
(*Projected timings in seconds:*)


(* ::Input:: *)
(*Table[HoldForm[10^#]&[x]->Floor[1.0186795297679153`*^-6 (10^x)^0.669307362337562`],{x,Range[13,20]}]*)


(* ::Subsubsection::Closed:: *)
(*Testing*)


(* ::Input:: *)
(*\[Xi]=10^7;*)
(*\[Upsilon]=Floor[10\[Xi]^(1/3)];*)


(* ::Input:: *)
(*AbsoluteTiming[*)
(*ppQ = SegmentedPrimePowerBaseSieve[1, 4643, PrimesInRange[Floor[Sqrt[\[Xi]/\[Upsilon]]]]];*)
(*\[CapitalLambda]=Table[If[ppQ[[i]] == 0, N[0,30], N[Log[ppQ[[i]]],30]], {i, Floor[Sqrt[\[Xi]/\[Upsilon]]]}];*)
(*\[Psi] = Accumulate[\[CapitalLambda]];*)
(*\[Mu]=MoebiusMuTable[\[Upsilon]];*)
(*]*)


(* ::Input:: *)
(*Clear[S1,S2,S3,S4]*)


(* ::Input:: *)
(*S1[x_,u_]:=S1[x,u]=\[Psi][[u]]*)


(* ::Input:: *)
(*(* 2163.2451119420306888968769243293838372000381919973285982620242`30. *)*)
(*S1[\[Xi],\[Upsilon]]*)


(* ::Input:: *)
(*S2[x_,u_]:=S2[x,u]=\[Mu][[1;;u]].LogGamma[Quotient[x, Range[u]] + N[1,30]]*)


(* ::Input:: *)
(*(* 9.9648618717380987745648841041186533092510390740466227577447795871`32.90620045770206*^6 *)*)
(*S2[\[Xi],\[Upsilon]]*)


(* ::Input:: *)
(*S3[x_,u_]:=S3[x,u]=-Sum[\[Mu][[l]]\[CapitalLambda][[m]]Quotient[x,l*m],{l,u},{m,u}]*)


(* ::Input:: *)
(*(* 30577.8701147474070596620456497825137776074924855723816235515616`25.878920646083962 *)*)
(*S3[\[Xi],\[Upsilon]]*)


(* ::Input:: *)
(*S4a[x_,u_]:=S4a[x,u]=-Sum[\[Mu][[l]]Sum[\[Psi][[Quotient[x,l*m]]]-\[Psi][[u]],{m,Quotient[u,l]+1,Min[Quotient[x,u*l],Floor[Sqrt[x/l]]]}],{l,u}]*)


(* ::Input:: *)
(*(* 636533.0558568085168511837440337595751365333148393155519122802848`27.980761950538337 *)*)
(*S4a[\[Xi],\[Upsilon]]*)


(* ::Input:: *)
(*S4b[x_,u_]:=S4b[x,u]=-Sum[\[Mu][[l]]Sum[\[Psi][[Quotient[x,l*m]]]-\[Psi][[u]],{m,Floor[Sqrt[x/l]]+1,Quotient[x,u*l]}],{l,u}]*)


(* ::Input:: *)
(*(* -635596.6394756213628117286083371928052204207426113240702063030993`28.93332318859407 *)*)
(*S4b[\[Xi],\[Upsilon]]*)


(* ::Input:: *)
(*(* 9.9985394033459753663528981623893319767819591772907785385087833642`28.32045464160814*^6 *)*)
(*Total@Through[{S1,S2,S3,S4a, S4b}[\[Xi],\[Upsilon]]]*)


(* ::Subsection::Closed:: *)
(*ChebyshevTheta*)


(* ::Subsubsection::Closed:: *)
(*Compiled... major rounding errors, but fast*)


(* ::Text:: *)
(*I wish I could do*)
(*int z = *((int * ) & ((float)x));*)
(*int log2 = ((z >> 23) & 0xFF) - 127;*)


log2 = fastCompile[{{x, _Integer}},
	Module[{lg, pow2},
		lg = Floor[Log[2, x]]-1;
		pow2 = 2^lg;

		Which[
			4pow2 <= x, lg+2,
			2pow2 <= x, lg+1,
			True, lg
		]
	]
];


(* ::Text:: *)
(*NOTE: since compile can only perform machine precision arithmetic, error occurs. Around 10^12 and up, the absolute error is > 0.1*)


ChebyshevTheta = fastCompile[{{x, _Integer}},
	Module[{cbrt = Floor[x^(1/3)], primes, pQ, \[CurlyTheta], lg, xpows},
		primes = PrimesInRangeCompiled[Floor[Sqrt[cbrt]]];

		pQ = SegmentedPrimeQSieve[1, cbrt, 1, primes];
		\[CurlyTheta] = accumulateReal[Table[If[pQ[[i]] == 0, 0., Log[i]], {i, cbrt}]];

		xpows = Floor[x^(1/Range[3, log2[x], 2])];

		ChebyshevPsi[x] - ChebyshevPsi[Floor[Sqrt[x]]] - Total[\[CurlyTheta][[xpows]]]
	]
];


(* ::Subsubsection::Closed:: *)
(*Uncompiled... no rounding errors, but slow*)


ChebyshevThetaSlow[x_] := Module[{cbrt = Floor[x^(1/3)], primes, \[CurlyTheta], xpows, p, sqrt},
	p = 2If[ExactNumberQ[x], MachinePrecision, Precision[x]];

	primes = PrimesInRangeCompiled[Floor[Sqrt[cbrt]]];

	\[CurlyTheta] = Accumulate[log /@ N[Range[cbrt] * SegmentedPrimeQSieve[1, cbrt, 1, primes], p]];
	xpows = Floor[x^(1/Range[3, log2[Floor[x]], 2])];

	If[p == 2MachinePrecision, 
		p = Sequence[], 
		p = p/2
	];

	sqrt = If[ExactNumberQ[x], Floor[Sqrt[x]], Sqrt[x]];
	N[ChebyshevPsiSlow[x] - ChebyshevPsiSlow[sqrt] - Total[\[CurlyTheta][[xpows]]], p]
];


(* ::Subsection::Closed:: *)
(*Primorial*)


Primorial[x_] := Module[{p},
	p = 2If[ExactNumberQ[x], MachinePrecision, Precision[x]];
	N[Exp[ChebyshevThetaSlow[N[x, p]]], p/2]
]


(* ::Subsection::Closed:: *)
(*PrimePi*)


(* ::Text:: *)
(*This is an implementation of the classic LMO algorithm described here. Since this was written in Mathematica, I could not make optimizations such as using bit arrays, being cache aware, etc, so this code is orders of magnitude slower than it could be.*)


(* ::Text:: *)
(*However the runtime isn't terrible: Prime\[Pi][10^16] takes about an hour. (See the runtime section for more timings and asymptotic runtime)*)


(* ::Subsubsection::Closed:: *)
(*S3*)


BinaryExponents = fastCompile[{{n, _Integer}, {w, _Integer}},
	Module[{i = 0, x = n, lis = Table[0, {w}]},
		While[x != 0,
			i--;
			lis[[i]] = Mod[x, 2];
			x = Quotient[x, 2];
		];
		Select[Range[w, 1, -1]lis, Positive] - 1
	]
];


BinaryExponents2 = fastCompile[{{n, _Integer}},
	Module[{m = n, len = 0, tbl, i = 0},
		While[m != 0,
			len += Mod[m, 2];
			m = Quotient[m, 2]
		];

		tbl = Table[0, {len}];
		m = n;

		While[m != 0,
			If[Mod[m, 2] == 1,
				tbl[[len--]] = i
			];
			i++;
			m = Quotient[m, 2]
		];

		tbl
	]
];


iS3 = fastCompile[{{x, _Integer}, {y, _Integer}, {primes, _Integer, 1}, {\[Mu], _Integer, 1}},
	Module[{\[Delta], S = 0, sieve, L1 = 1, L2 = 1, CAP = Ceiling[x/y], lg2y, \[CurlyPhi]old, acache, a, \[CurlyPhi]cache = {0, 0}, \[CurlyPhi]=0, qq, yy, b, e, f=0},
		\[Delta] = SegmentedLeastPrimeFactorSieve[1, y, 1, primes];
		lg2y = IntegerLength[y, 2] - 1;

		\[CurlyPhi]old = Table[0, {Length[primes]+1}];
		acache = Table[If[j*2^i > y, Max[y-(j-1)*2^i, 0], 2^i], {i, 0, lg2y}, {j, 1, y(*Quotient[y, 2^i]*)+1}];

		While[L2 < CAP,
			L2 = Min[L1 + y-1, CAP];
			sieve = Table[1, {L2 - L1 + 1}];

			a = acache;

			b = 0;
			Do[
				b++;

				\[CurlyPhi]cache = {0, 0};
				Do[
					If[\[Delta][[m]] <= p || \[Mu][[m]] == 0, Continue[]];
					qq = Quotient[x, m*p];
					If[qq == \[CurlyPhi]cache[[1]], S -= \[Mu][[m]]\[CurlyPhi]cache[[2]]; Continue[]];

					If[b == 1,
						\[CurlyPhi] = qq,
						e = BinaryExponents[qq - L1 + 1, lg2y+1];
						\[CurlyPhi] = \[CurlyPhi]old[[b]];
						Do[
							If[r == 1, f = 0, f = 2^(e[[r-1]]-e[[r]])(f+1)];
							\[CurlyPhi] += a[[e[[r]]+1, f+1]], 
							{r, Length[e]}
						]
					];

					S -= \[Mu][[m]]\[CurlyPhi];
					\[CurlyPhi]cache = {qq, \[CurlyPhi]},
					{m, Max[Quotient[y, p], Quotient[x, p*(L2+1)]] + 1, Min[y, Quotient[x, p*L1]]}
				];

				If[b == 1,
					\[CurlyPhi]old[[b]] = L2,
					e = BinaryExponents[L2 - L1 + 1, lg2y+1];
					\[CurlyPhi] = \[CurlyPhi]old[[b]];
					Do[
						If[r == 1, f = 0, f = 2^(e[[r-1]]-e[[r]])(f+1)];
						\[CurlyPhi] += a[[e[[r]]+1, f+1]], 
						{r, Length[e]}
					];
					\[CurlyPhi]old[[b]] = \[CurlyPhi]
				];

				yy = Quotient[L1-1, p];
				Do[
					If[sieve[[k - L1 + 1]] != 0,
						qq = k-L1;
						Do[a[[i, qq+1]] -= 1; If[qq > 0, qq = Quotient[qq, 2]], {i, 1, lg2y+1}];
						sieve[[k - L1 + 1]] = 0
					],
					{k, p*yy+(Boole[p!=2&&Mod[yy,2]==1]+1)p, p*Quotient[L2, p], (Boole[p!=2]+1)p}
				],
				{p, primes}
			];

			L1 = L2 + 1
		];

		S
	]
];


(* ::Input:: *)
(*\[Xi]=10^11;*)
(*\[Psi]=getY[\[Xi]];*)
(*\[Pi]rimes=PrimesUpTo[Max[\[Xi]^(1/4),Sqrt[\[Psi]]]];*)
(*m=MoebiusMuUpTo[\[Psi]];*)


(* ::Input:: *)
(*(* 4744412960 *)*)
(*iS3[\[Xi],\[Psi],\[Pi]rimes,m]//AbsoluteTiming*)


(* ::Subsubsection::Closed:: *)
(*Prime\[Pi] (Main)*)


getY = fastCompile[{{x, _Integer}},
	100Floor[Floor[x^.4]/100]
];


(* ::Input:: *)
(*(* isPrime(x) \[Equal] PrimePi[x] - PrimePi[x-1] *)*)
(*(* NextPrime\[GreaterEqual](x) \[Equal] Prime[PrimePi[x-1] + 1] *)*)
(*(* NextPrime>(x) \[Equal] Prime[PrimePi[x] + 1] *)*)
(*(* PrevPrime\[LessEqual](x) \[Equal] Prime[PrimePi[x]] *)*)
(*(* PrevPrime<(x) \[Equal] Prime[PrimePi[x-1]] *)*)


Prime\[Pi] = fastCompile[{{x, _Integer}},
	Module[{primes, y = getY[x], \[Pi]y, \[Pi]x13, \[Mu], CAP, L1, L2 = 0, \[Pi]old = 0, sqrt, cbrt, x14, ceilsqrt, floorsqrt, pQ, pismall, pis, \[ScriptCapitalP], 
			m1, m2, \[ScriptP], q, z, s = 0, r = 0, w, qq, p14, min, max, \[ScriptCapitalP]W1 = {0}, \[ScriptCapitalP]W2, W1Q, W2Q, primeQ, b = 1,
			P = 0, \[CurlyPhi] = 0, S0, S, S1, S3, U, V, V1, W1 = 0, W2 = 0, W3 = 0, W4, W5 = 0},
		sqrt = Floor[Sqrt[x] + 0.000001];
		cbrt = Floor[x^(1/3) + 0.000001];
		x14 = Floor[x^(1/4) + 0.000001];
		(*y = Floor[x^(1/3)Log[Log[x]]];*)
		CAP = Ceiling[x/y];
		floorsqrt = Floor[Sqrt[x/y] + 0.000001];
		ceilsqrt = Ceiling[Sqrt[x/y]];

		primes = PrimesInRangeCompiled[y];

		pQ = SegmentedPrimeQSieve[1, y, 1, primes];
		pismall = accumulate[pQ];
		
		\[Pi]y = \[Pi]old = pismall[[y]];
		\[Pi]x13 = pismall[[Floor[x^(1/3)]]];

		\[Mu] = SegmentedMoebiusMuSieve[1, y, 1, primes];

		(* ------------------------------------ *)
		(* --- All PrimePi[z] for 1 \[LessEqual] z \[LessEqual] y --- *)
		(* ------------------------------------ *)

		(* In this section we compute *)
		(* All of  S0, S1, U, V1, W4, W5 *)
		(* Part of W2 *)

		S0 = \[Mu].Quotient[x, Range[y]];
		S1 = Quotient[(\[Pi]y - \[Pi]x13)(\[Pi]y - \[Pi]x13 - 1), 2];

		\[ScriptCapitalP] = primes[[pismall[[floorsqrt]] + 1 ;; pismall[[cbrt]]]];
		U = Sum[\[Pi]y - pismall[[Quotient[x, p^2]]], {p, \[ScriptCapitalP]}];

		V1 = Sum[(i - \[Pi]y)(i - 2), {i, pismall[[x14]] + 1, pismall[[floorsqrt]]}];
		Do[V1 += (pismall[[Quotient[x, p^2]]] - pismall[[p]])(2 - pismall[[p]]), {p, primes[[pismall[[floorsqrt]] + 1 ;; pismall[[cbrt]]]]}];

		(* W2 *)
		\[ScriptCapitalP]W2 = primes[[pismall[[Max[x14, Quotient[x, y^2]]]] + 1 ;; pismall[[floorsqrt]]]];
		Do[
			qq = Quotient[x, p(y+1)]+1;
			min = Max[pismall[[p]]+1, pismall[[qq]] + 1-pQ[[qq]]];
			max = pismall[[Min[Quotient[x, p], Floor[Sqrt[x/p]]]]];
			If[min > max, Continue[]];
			W2 += Total[pismall[[Quotient[x, p*primes[[min ;; max]]]]]],
			{p, \[ScriptCapitalP]W2}
		];

		(* W3 *)
		w = If[pismall[[y]] != pismall[[y-1]], y, primes[[pismall[[y]]]]];
		\[ScriptCapitalP] = \[ScriptCapitalP]W2(*primes\[LeftDoubleBracket]pismall\[LeftDoubleBracket]Min[x14, Quotient[x, y^2]]\[RightDoubleBracket] + 1 ;; pismall\[LeftDoubleBracket]floorsqrt\[RightDoubleBracket]\[RightDoubleBracket]*);
		Do[
			qq = pismall[[Floor[Sqrt[x/p] + 0.000001]]] + 1;
			If[qq > pismall[[y]], Continue[]];
			q = primes[[qq]];
			While[True,
				z = Quotient[x, p*q];
				s = If[pismall[[z]] != pismall[[z-1]], z, primes[[pismall[[z]]]]];
				qq = Min[Quotient[x, p*s], y];
				r = Min[If[pismall[[qq]] != pismall[[qq-1]], qq, primes[[pismall[[qq]]]]], w];
				W3 += (pismall[[r]] - pismall[[q]] + 1)*pismall[[z]];
				If[r == w, Break[]];
				q = primes[[pismall[[r]] + 1]];
			],
			{p, \[ScriptCapitalP]}
		];

		(* W4 *)
		W4 = Sum[
			If[pismall[[p]] + 1 <= pismall[[Floor[Sqrt[x/p] + 0.000001]]],
				Total[pismall[[Quotient[x, p*primes[[pismall[[p]] + 1 ;; pismall[[Floor[Sqrt[x/p] + 0.000001]]]]]]]]],
				0
			],
			{p, primes[[pismall[[ceilsqrt]] + Boole[pismall[[ceilsqrt]] == pismall[[ceilsqrt-1]]] ;; pismall[[cbrt]]]]}
		];

		(* W5 *)
		\[ScriptCapitalP] = primes[[pismall[[Floor[Sqrt[x/y]]]] + 1 ;; pismall[[cbrt]]]];
		Do[
			q = primes[[pismall[[Floor[Sqrt[x/p]]]] + 1]];
			qq = Quotient[x, p^2];
			w = If[pismall[[qq]] != pismall[[qq-1]], qq, primes[[pismall[[qq]]]]];
			While[True,
				z = Quotient[x, p*q];
				s = If[pismall[[z]] != pismall[[z-1]], z, primes[[pismall[[z]]]]];
				qq = Min[Quotient[x, p*s], y];
				r = Min[If[pismall[[qq]] != pismall[[qq-1]], qq, primes[[pismall[[qq]]]]], w];
				W5 += (pismall[[r]] - pismall[[q]] + 1)*pismall[[z]];
				If[r == w, Break[]];
				q = primes[[pismall[[r]] + 1]];
			],
			{p, \[ScriptCapitalP]}
		];

		(* -------------------------------------------- *)
		(* --- All PrimePi[z] for y+1 \[LessEqual] z \[LessEqual] Sqrt[x] --- *)
		(* -------------------------------------------- *)

		(* In this section we compute *)
		(* All of  W1 *)
		(* Part of W2 *)

		(*p14 = pismall\[LeftDoubleBracket]x14\[RightDoubleBracket] + pQ\[LeftDoubleBracket]x14\[RightDoubleBracket];*)
		W1Q = Boole[pismall[[x14]] + 1 <= pismall[[Quotient[x, y^2]]]];
		If[W1Q == 1, \[ScriptCapitalP]W1 = primes[[pismall[[x14]] + 1 ;; pismall[[Quotient[x, y^2]]]]]];

		L1 = y+1;
		While[L2 < sqrt,
			L2 = Min[L1 + y, sqrt];
			primeQ = SegmentedPrimeQSieve[L1, L2, 1, primes];
			pis = \[Pi]old + accumulate[primeQ];
			\[Pi]old = Last[pis];

			If[W1Q == 1,
				Do[
					qq = Quotient[x, p(L2+1)]+1;
					min = Max[pismall[[p]]+1, pismall[[qq]] + 1-pQ[[qq]]];
					max = pismall[[Min[Quotient[x, L1 p], y]]];
					If[min > max, Break[]];
					W1 += Total[pis[[Quotient[x, p*primes[[min ;; max]]] - L1 + 1]]],
					{p, \[ScriptCapitalP]W1}
				]
			];

			Do[
				If[p >= Sqrt[x/L1], Break[]];
				min = pismall[[Max[p, Quotient[x, p(L2+1)]]]]+1;
				max = pismall[[Min[Quotient[x, L1 p], Floor[Sqrt[x/p]]]]];
				If[min > max, Continue[]];
				W2 += Total[pis[[Quotient[x, p*primes[[min ;; max]]] - L1 + 1]]],
				{p, \[ScriptCapitalP]W2}
			];

			L1 = L2 + 1
		];

		(* -------------------------------------------- *)
		(* --- All PrimePi[z] for Sqrt[x] < z \[LessEqual] x/y --- *)
		(* -------------------------------------------- *)

		(* In this section we compute *)
		(* Part of W2 *)

		P = -Quotient[(\[Pi]old - \[Pi]y)*(\[Pi]old + \[Pi]y - 1), 2];

		W2Q = Boole[y^4 > x*sqrt];
		While[L2 < CAP,
			L2 = Min[L1 + y, CAP];
			pis = \[Pi]old + accumulate[SegmentedPrimeQSieve[L1, L2, 1, primes]];
			\[Pi]old = Last[pis];
			\[ScriptCapitalP] = SegmentedPrimeSieve[Max[Quotient[x, L2+1], y]+1, Min[Quotient[x, L1], sqrt], 1, primes];

			P += Sum[pis[[Quotient[x, p] - L1 + 1]], {p, \[ScriptCapitalP]}];

			If[W2Q == 1,
				Do[
					If[p >= Sqrt[x/L1], Break[]];
					min = pismall[[Max[p, Quotient[x, p(L2+1)]]]]+1;
					max = pismall[[Min[Quotient[x, L1 p], Floor[Sqrt[x/p]]]]];
					If[min > max, Continue[]];
					W2 += Total[pis[[Quotient[x, p*primes[[min ;; max]]] - L1 + 1]]],
					{p, \[ScriptCapitalP]W2}
				];
			];

			L1 = L2 + 1
		];

		S3 = iS3[x, y, primes[[1 ;; pismall[[x14]]]], \[Mu]];

		(*Print[{S0, S1, U, V1, W1, W2, W3, W4, W5, S3, \[Pi]y-1, -P}];*)
		S0+S1+U+V1+W1+W2+W3+W4+W5+S3+\[Pi]y-1-P
	]
];


(* ::Input:: *)
(*Prime\[Pi][10^13]//AbsoluteTiming*)


(* ::Input:: *)
(*PrimePi[10^13]//AbsoluteTiming*)


(* ::Subsubsection::Closed:: *)
(*Testing correctness of subfunctions*)


(* ::Text:: *)
(*Brute force versions of subfunctions. Since these are brute force we know they are correct, so we can test our results against these.*)


(* ::Input:: *)
(*\[Xi]=10^13;*)
(*\[Psi]=150000;*)


(* ::Input:: *)
(*(* {S0, S1, U, V1, W1, W2, W3, W4, W5, PrimePi[y] - 1, P} *)*)
(*Prime\[Pi][\[Xi],\[Psi]]//AbsoluteTiming*)


S0[x_, y_] := S0[x, y] = MoebiusMuTable[Floor[y]].Quotient[x, Range[y]]


(* ::Input:: *)
(*S0[\[Xi],\[Psi]]*)


S1[x_, y_] := S1[x, y] = (PrimePi[y] - PrimePi[x^(1/3)])(PrimePi[y] - PrimePi[x^(1/3)] - 1)/2


(* ::Input:: *)
(*S1[\[Xi],\[Psi]]*)


U[x_, y_] := U[x, y] = With[{py = PrimePi[y]},
	Sum[py - PrimePi[x/p^2], {p, PrimesInRange[Floor[Sqrt[x/y]]+1, Floor[x^(1/3)]]}]
]


(* ::Input:: *)
(*U[\[Xi],\[Psi]]*)


V1[x_, y_] := V1[x, y] = Sum[Length[PrimesInRange[p+1, Floor[Min[x/p^2, y]]]](2 - PrimePi[p]), {p, PrimesInRange[Floor[x^(1/4)]+1, Floor[x^(1/3)]]}]


(* ::Input:: *)
(*V1[\[Xi],\[Psi]]*)


W1[x_, y_] := W1[x, y] = Sum[PrimePi[x/(p*q)], {p, PrimesInRange[Floor[x^(1/4)]+1, Floor[x/y^2]]}, {q, PrimesInRange[p+1, Floor[y]]}]


(* ::Input:: *)
(*W1[\[Xi],\[Psi]]*)


W2[x_, y_] := W2[x, y] = Sum[PrimePi[x/(p*q)], {p, PrimesInRange[Floor[Max[x^(1/4), x/y^2]]+1, Floor[Sqrt[x/y]]]}, {q, PrimesInRange[p+1, Floor[Sqrt[x/p]]]}]


(* ::Input:: *)
(*W2[\[Xi],\[Psi]]*)


W3[x_, y_] := W3[x, y] = Sum[PrimePi[x/(p*q)], {p, PrimesInRange[Floor[Max[x^(1/4), x/y^2]]+1, Floor[Sqrt[x/y]]]}, {q, PrimesInRange[Floor[Sqrt[x/p]]+1, Floor[y]]}]


(* ::Input:: *)
(*W3[\[Xi],\[Psi]]*)


W4[x_, y_] := W4[x, y] = Sum[PrimePi[x/(p*q)], {p, PrimesInRange[Floor[Sqrt[x/y]]+1, Floor[x^(1/3)]]}, {q, PrimesInRange[p+1, Floor[Sqrt[x/p]]]}]


(* ::Input:: *)
(*W4[\[Xi],\[Psi]]*)


W5[x_, y_] := W5[x, y] = Sum[PrimePi[x/(p*q)], {p, PrimesInRange[Floor[Sqrt[x/y]]+1, Floor[x^(1/3)]]}, {q, PrimesInRange[Floor[Sqrt[x/p]]+1, Floor[x/p^2]]}]


(* ::Input:: *)
(*W5[\[Xi],\[Psi]]*)


(* ::Input:: *)
(*PrimePi[\[Psi]] - 1*)


P[x_, y_] := P[x, y] = Sum[PrimePi[x/p] - PrimePi[p] + 1, {p, PrimesInRange[Floor[y]+1, Floor[Sqrt[x]]]}]


(* ::Input:: *)
(*P[\[Xi],\[Psi]]*)


(* ::Input:: *)
(*(pp[#]=PrimePi[#])&/@Range[1000];*)
(*(prime[#]=Prime[#])&/@Range[1000];*)


(* ::Input:: *)
(*\[Delta]=LeastPrimeFactorsTable[10^7];*)
(*\[Mu]=MoebiusMuTable[10^7];*)


(* ::Input:: *)
(*Clear[phi]*)
(*phi[x_,0]:=Floor[x]*)
(*phi[x_,n_]:=phi[x,n]=1+Length[Select[Range[x],\[Delta][[#]]>prime[n]&]]*)


\[ScriptCapitalS]3[x_, y_] := \[ScriptCapitalS]3[x, y] = Sum[Boole[\[Delta][[\[ScriptM]]] > p] \[Mu][[p \[ScriptM]]] phi[Floor[x/(\[ScriptM]*p)], pp[p]-1], {p, PrimesInRange[Floor[x^(1/4)]]}, {\[ScriptM], Floor[y/p] + 1, y}]


(* ::Input:: *)
(*\[ScriptCapitalS]3[\[Xi],\[Psi]]*)


(* ::Subsubsection::Closed:: *)
(*Testing correctness*)


(* ::Input:: *)
(*{PrimePi[10^10],Prime\[Pi][10^10]}*)


(* ::Input:: *)
(*{PrimePi[10^11],Prime\[Pi][10^11]}*)


(* ::Input:: *)
(*{PrimePi[10^12],Prime\[Pi][10^12]}*)


(* ::Input:: *)
(*{PrimePi[10^13],Prime\[Pi][10^13]}*)


(* ::Input:: *)
(*{PrimePi[10^14],Prime\[Pi][10^14]}*)


(* ::Subsubsection::Closed:: *)
(*Runtimes*)


(* ::Input:: *)
(*Table[AbsoluteTiming[Prime\[Pi][10^n]],{n,10,14}]*)


(* ::Input:: *)
(*Prime\[Pi][10^15]//AbsoluteTiming*)


(* ::Input:: *)
(*Prime\[Pi][10^16]//AbsoluteTiming*)


(* ::Input:: *)
(*Prime\[Pi][10^17]//AbsoluteTiming*)


(* ::Input:: *)
(*\[Pi]18=AbsoluteTiming[Prime\[Pi][10^18]]*)


(* ::Input:: *)
(*(* Runtimes for Prime\[Pi][10^Range[10,18]] *)*)
(*data=Transpose[{Range[10,18],Log10@({0.63771100000000002783195895972312428057`5.825223821560746,2.6322130000000001359694579150527715683`6.4409209429714585,11.34979300000000002057731762761250138283`7.075587854123519,50.35642200000000201498551177792251110077`7.72265477766898,213.07050599999999462852429132908582687378`8.349123250521052,921.91053099999999176361598074436187744141`8.985288689237406,4079.14168100000006234040483832359313964844`9.63116870322724,17157.1620990000010351650416851043701171875`10.255045367732336,71718.70097299999906681478023529052734375`10.87623232794881}/1.36343938482415031672038172672342831715`6.702043385700776)}];*)


(* ::Input:: *)
(*(* 3.39487*10^-7 x^0.621677 *)*)
(*N[a x^b/.FindFit[10^SetPrecision[data,25],a x^b,{a,b},x,WorkingPrecision->20]]*)


(* ::Input:: *)
(*ListLinePlot[data]*)


(* ::Section::Closed:: *)
(*End*)


End[];
EndPackage[];
