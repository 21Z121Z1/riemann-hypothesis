import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0439
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
import Formalism.LocalToGlobal.HermitianForms.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCoefficientCompatibility
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfMem
section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.Col2.ChiFinTop

open GlobalTheory.Mem.Col2.PtExist

theorem exists_isPtOf_of_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q = ∅)
    {g : GL (Fin n) (AfE F E)} (hg : g ∈ UAd hc n) : ∃ p : DecoF E n ST SG Q, IsPtOf hc g p := by
  classical
  obtain ⟨p, hd, -⟩ := GlobalTheory.Mem.ColAd.exists_near (ST := ST) (SG := SG) (Q := Q) hc 0 hg
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := congrArg Deco.N hd
  refine ⟨p, hg, hN ▸ carries_globLat g, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P => absurd P.2 (by simp [hQ])⟩
  · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
    rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv), e]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)
  · rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv)]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)

theorem chi_top_root_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (K : ClsTied (D := (I.rec7 l Z)) u B.R.m le_rfl), (∃ k, I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k) → ∃ n : ℕ, 0 < n ∧ ∀ x : K.lev.U, ((K.lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : B.LL, B.embLL r = ((K.lev.chi x : ℂˣ) : ℂ) := by
  intro B X I hI hP l Z u K ⟨k, hR⟩
  obtain ⟨c, -⟩ := hR.onto ()
  have hpt := hR.pt c
  have hg1 : gramN (I.rec7 l Z) B.R.m le_rfl = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 B.R.m le_rfl).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) B.R.m le_rfl) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      UAd B.sp.cm (B.R.N B.R.m) := by rw [hg1]; rfl
  have hxU : ∀ x : K.lev.U, x.1 ∈ UAd B.sp.cm (B.R.N B.R.m) := fun x => eU ▸ ((K.lev.U_eq x.1).1 x.2).1
  have hyk := hpt.uni
  obtain ⟨p0, hp0, -⟩ := hR.k_std ()
  have hk := hp0.uni
  have hQ : I.Q I.mu0 = ∅ := by
    show QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅
    rw [I.trueColumn_tuple_trivial_eq_one]
    exact twistPrimes_trivialTuple_empty I.sel I.S

  have hQ' : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := hQ
  obtain ⟨N, hN, hroot⟩ : ∃ N, 0 < N ∧ ∀ κ : (I.stp u I.mu0 B.R.m).G c.1, (I.stp u I.mu0 B.R.m).chr c.1 κ ^ N = 1 := by
    let Λ := levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) B.R.m c.1
    let Θ := levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) B.R.m c.1
    haveI : Subsingleton ↥Θ.grp := ⟨fun a b => Subtype.ext (funext fun P => absurd P.2 (by simp [hQ']))⟩
    haveI : Finite ↥Λ.grp := inferInstance
    refine ⟨Nat.card (↥Λ.grp × ↥Θ.grp), Nat.card_pos, fun κ => ?_⟩
    have h2 : κ.2 ^ Nat.card (↥Λ.grp × ↥Θ.grp) = 1 := pow_card_eq_one'
    rw [← map_pow]
    show Λ.chr ((κ ^ Nat.card (↥Λ.grp × ↥Θ.grp)).2.1) * Θ.chr ((κ ^ Nat.card (↥Λ.grp × ↥Θ.grp)).2.2) = 1
    rw [Prod.pow_snd, h2]
    simp
  haveI : NeZero (B.R.N B.R.m) := ⟨(B.R.N_pos B.R.m).ne'⟩
  refine ⟨N, hN, fun x => ?_⟩
  let yc : GA B (B.R.N B.R.m) := (K.y c).1
  let xg : GA B (B.R.N B.R.m) := x.1
  have hxg : xg ∈ UAd B.sp.cm (B.R.N B.R.m) := hxU x
  have hyk' : yc * k () ∈ UAd B.sp.cm (B.R.N B.R.m) := hyk
  have hg : yc * xg * k () ∈ UAd B.sp.cm (B.R.N B.R.m) := by
    have h1 : yc * xg * k () = (yc * k ()) * ((k ())⁻¹ * xg * k ()) := by group
    rw [h1]
    exact mul_mem hyk' (mul_mem (mul_mem (inv_mem hk) hxg) hk)
  obtain ⟨q, hq⟩ := GlobalTheory.Mem.Col2.ChiFinTop.exists_isPtOf_of_mem (ST := (B.primes X).vT u) (SG := (B.primes X).vGs)
    (Q := QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) B.sp.cm hQ' hg
  obtain ⟨κ, hgam, hκq, -⟩ := (hR.lev c x.1 q hq).1 x.2
  have hchi : ((K.lev.chi x : ℂˣ) : ℂ) = B.embLL (((I.stp u I.mu0 B.R.m).chr c.1 κ : B.LLˣ) : B.LL) :=
    hR.chr c x κ hgam (by rw [hκq]; exact hq)
  refine ⟨by rw [hchi, ← map_pow, ← Units.val_pow_eq_pow_val, hroot κ, Units.val_one, map_one], _, hchi.symm⟩

end GlobalTheory.Mem.Col2.ChiFinTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelOfLinearMap
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PtId.OneScalar

theorem map_pG_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c c' : Coeff l) (φ : c.F →+* ℂ) (φ' : c'.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    MvPolynomial.map φ (pG (Dw := Dw) c a n) = MvPolynomial.map φ' (pG (Dw := Dw) c' a n) := by
  have h : ∀ s i hi col, MvPolynomial.map φ (minorPolynomial (Dw := Dw) (n := n) c s i hi col) =
      MvPolynomial.map φ' (minorPolynomial c' s i hi col) := by
    intro s i hi col
    unfold minorPolynomial
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext p q : 2
    simp
  unfold pG
  simp only [map_prod, map_pow]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => ?_
  congr 1
  split_ifs
  · exact h _ _ _ _
  · exact h _ _ _ _
  · rw [map_zero, map_zero]

theorem ten_extremal_mem (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    (Formalism.L2.DIV.ten fun τ => extremal K n (lam τ)) ∈ Formalism.L2.DIV.VV K lam :=
  GlobalTheory.Proof.TensorMapDescent.ten_mem lam _ fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (Formalism.L2.DIV.natW_antitone (lam τ))

theorem lt_injective {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} (hH : ∀ ρ, tauE D ρ (H.rt : D.host.E) = H.rt0)
    {m n : ℕ} (lt : LtN Dw n → FVar D m n)
    (hlt : ∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨
      (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = Dw.p + ℓ.2.1))) : Function.Injective lt := by
  have hp : ∀ ℓ : LtN Dw n, ∀ ρ, ℓ.1 = tauE D ρ → (ℓ.2.1 : ℕ) < Dw.p := by
    rintro ⟨σ, s, b⟩ ρ h
    have hs := s.2
    have : Dw.mult σ = Dw.p := by
      rw [show σ = tauE D ρ from h]
      exact if_pos (hH ρ)
    exact this ▸ hs
  intro x y hxy
  obtain ⟨a1, a2⟩ := hlt x
  obtain ⟨b1, b2⟩ := hlt y
  have hpx := hp x (lt x).1
  have hpy := hp y (lt y).1
  rw [hxy] at a1 a2 hpx
  have key : x.1 = y.1 ∧ (x.2.1 : ℕ) = y.2.1 := by
    rcases a2 with ⟨a2, a3⟩ | ⟨a2, a3⟩ <;> rcases b2 with ⟨b2, b3⟩ | ⟨b2, b3⟩
    · exact ⟨a2.trans b2.symm, by omega⟩
    · have := hpx a2; omega
    · have := hpy b2; omega
    · exact ⟨a2.trans b2.symm, by omega⟩
  obtain ⟨σ, s, b⟩ := x
  obtain ⟨σ', s', b'⟩ := y
  obtain ⟨k1, k2⟩ := key
  dsimp only at k1 k2 a1 b1
  subst k1
  obtain rfl : s = s' := Fin.ext k2
  obtain rfl : b = b' := a1.symm.trans b1
  rfl

section Hw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}

theorem coefficientMap_extremalTensor_baseChange {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (hO : hwOK O.c' (lamV D i) O.hw)
    {c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W} (hc : CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0') :
    O.c0' O.hw = c0L ⟨_, ten_extremal_mem D.what₂.LL (lamV D i)⟩ := by
  obtain ⟨v', h1, h2⟩ := hc ⟨_, ten_extremal_mem D.what₂.LL (lamV D i)⟩
  rw [← h2]
  congr 1
  apply Subtype.ext
  rw [h1, show (O.hw : Formalism.L2.DIV.Pol O.c'.F D.what₂.Tau (Vc D i).rank) = _ from hO]
  dsimp only
  rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
  simp only [Formalism.L2.DIV.map_extremal]

end Hw

theorem exists_scalar : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W), ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0' → GlobalTheory.PtId.IoAt O (v₀ i (sg0 D A)) ka := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT hI i c0L
  by_cases hex : ∃ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup),
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) ∧ CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0'
  swap
  · exact ⟨1, norm_one, fun Tp tup O h1 h2 => absurd ⟨Tp, tup, O, h1, h2⟩ hex⟩
  obtain ⟨Tp₀, tup₀, O₀, hP₀, hB₀⟩ := hex
  obtain ⟨ka₀, hn₀, hk₀⟩ := GlobalTheory.T.oscillator_model_extension_first D G Pl0 T0 A T R F κ v₀ hC hT hI i Tp₀ tup₀ O₀ hP₀
  refine ⟨ka₀, hn₀, fun Tp tup O hP hB => ?_⟩
  obtain ⟨ka, -, hk⟩ := GlobalTheory.T.oscillator_model_extension_first D G Pl0 T0 A T R F κ v₀ hC hT hI i Tp tup O hP
  intro lt hlt u hu
  suffices h : ka = ka₀ by
    subst h
    exact hk lt hlt u hu
  have e1 := hk lt hlt u hu A.μ0 O.hw
  have e2 := hk₀ lt hlt u hu A.μ0 O₀.hw
  obtain ⟨hw1, cga, -, hinj, -, -, -, -, hio, -⟩ := hP.io
  obtain ⟨hw2, cga', -, -, -, -, -, -, hio₀, -⟩ := hP₀.io
  have hne : O.io O.hw ≠ 0 := by
    intro h0
    have h1 : O.hw = 0 := hinj (h0.trans (map_zero _).symm)
    have h2 := (GlobalTheory.AdTh.coefMap_norm_equivariant_basis D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup O hP).1
    rw [h1, map_zero, norm_zero] at h2
    exact zero_ne_one h2
  rw [coefficientMap_extremalTensor_baseChange O hw1 hB] at e1
  rw [coefficientMap_extremalTensor_baseChange O₀ hw2 hB₀, hio₀, map_pG_eq O₀.c' O.c' (inC O₀.c') (inC O.c'), ← hio, e1] at e2
  have hV := hP.lift.std
  obtain ⟨f1, f2, f3, f4, f5⟩ := GlobalTheory.AdTh.VecFock.vec_fock D G Pl0 T0 A T.Q.c.F R F hC i A.μ0 hV
  have hON : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ => by
    refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩
    · simp [gramAt, hV.1]
    · simp
  have hinjP := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) (hC.thP.ωP i A.μ0).std hC.models.inf
    (fun _ => 1) (fun _ => 1) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) _ f4 f3 hON f5
    (D.sp.V_sig _) (D.sp.W_sig _) (R.vP i A.μ0) f1 f2 (GlobalTheory.AdTh.VecNe.thetaVector_ne_zero D G Pl0 T0 A T.Q.c.F R F hC i hV)
  have hlti : Function.Injective lt := lt_injective (fun ρ => hT.laws.pins.1.2.2.2 ρ) lt hlt
  refine smul_left_injective ℂ (fun h0 => hne ?_) e2
  have h1 := hinjP (h0.trans (map_zero _).symm)
  have h2 := MvPolynomial.rename_injective lt hlti (h1.trans (map_zero _).symm)
  exact MvPolynomial.map_injective _ (inC O.c').injective (h2.trans (map_zero _).symm)

end GlobalTheory.PtId.OneScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.BasePoint

open GlobalTheory.Mem.Col2.PtExist

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

private lemma mem_divs_iff' {E : Type} [Field E] [NumberField E] {π : 𝓞 E} {P : HeightOneSpectrum (𝓞 E)}
    (h : P ∈ divs π) : π ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · simpa using h
  · simp at h

private lemma false_of_mem_of_conj_mem_of_isCoprime {E : Type} [Field E] [NumberField E] [StarRing E] {π : 𝓞 E} (hcp : IsCoprime π (cO E π))
    (P : HeightOneSpectrum (𝓞 E)) (h1 : π ∈ P.asIdeal) (h2 : cO E π ∈ P.asIdeal) : False := by
  obtain ⟨u, v, h⟩ := hcp
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

private lemma valued_algebraMap_int_le_one' {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1 := by
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one P r

private lemma valued_algebraMap_eq_one_of_not_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E)
    (hr : r ∉ P.asIdeal) : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) = 1 := by
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap]
  have h2 : ¬ P.intValuation r < 1 := fun h => hr ((HeightOneSpectrum.intValuation_lt_one_iff_mem P r).1 h)
  exact le_antisymm (HeightOneSpectrum.intValuation_le_one P r) (not_lt.1 h2)

private lemma valued_inv_algebraMap_le_one_of_not_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E)
    (hr : r ∉ P.asIdeal) : Valued.v (algebraMap E (P.adicCompletion E) ((algebraMap (𝓞 E) E r)⁻¹)) ≤ 1 := by
  rw [map_inv₀, map_inv₀, valued_algebraMap_eq_one_of_not_mem P r hr, inv_one]

private lemma mem_RInt_of_valued_le_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (y : AfE F E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (adAt F P y) ≤ 1) : y ∈ RInt F E :=
  (GlobalTheory.Mem.Col2.mem_rInt_iff F E y).2 h

theorem exists_unit (hc : Formalism.BasicNotions.CMData F E) {π : 𝓞 E} (h0 : π ≠ 0) (h1 : cO E π ≠ 0) (hcp : IsCoprime π (cO E π)) :
    ∃ a a' : AfE F E, a' * a = 1 ∧ sigR hc.sig (FiniteAdeleRing (𝓞 F) F) a = a' ∧ a ∈ RInt F E ∧ a' ∈ RInt F E ∧
      (∀ P ∈ divs π, adAt F P a' = algebraMap E _ (algebraMap (𝓞 E) E (cO E π))) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), π * cO E π ∉ w.asIdeal → adAt F w a = 1 := by
  classical
  have hmem : ∀ {P : HeightOneSpectrum (𝓞 E)}, P ∈ divs π → π ∈ P.asIdeal := fun h => mem_divs_iff' h
  have hQ : ∀ P ∈ divs π, conjPrime₂ P ∉ divs π := by
    intro P hP hP'
    exact false_of_mem_of_conj_mem_of_isCoprime hcp P (hmem hP) ((mem_conjP P π).1 (hmem hP'))
  have hc0 : (algebraMap (𝓞 E) E (cO E π)) ≠ 0 := by
    intro h
    exact h1 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).1 h)
  have hst : star (algebraMap (𝓞 E) E (cO E π)) = algebraMap (𝓞 E) E π := by
    change star (starRingEnd E (algebraMap (𝓞 E) E π)) = _
    rw [starRingEnd_apply, star_star]
  let α : HeightOneSpectrum (𝓞 E) → E := fun _ => (algebraMap (𝓞 E) E (cO E π))⁻¹
  let β : HeightOneSpectrum (𝓞 E) → E := fun _ => algebraMap (𝓞 E) E (cO E π)
  let a := GlobalTheory.Mem.Col2.PtExist.glue hc (divs π) 1 α β
  have ha : ∀ w, adAt F w a = if w ∈ divs π then algebraMap E _ (α w)
      else if conjPrime₂ w ∈ divs π then algebraMap E _ (star (β (conjPrime₂ w))) else 1 := fun w => by
    rw [GlobalTheory.Mem.Col2.PtExist.adAt_glue hc (divs π) hQ 1 α β w, map_one]
  have ha' : ∀ w, adAt F w (sigR hc.sig (FiniteAdeleRing (𝓞 F) F) a) = if w ∈ divs π then algebraMap E _ (β w)
      else if conjPrime₂ w ∈ divs π then algebraMap E _ (star (α (conjPrime₂ w))) else 1 := fun w => by
    rw [GlobalTheory.Mem.Col2.PtExist.sig_glue hc (divs π) 1 α β, map_one,
      GlobalTheory.Mem.Col2.PtExist.adAt_glue hc (divs π) hQ 1 β α w, map_one]
  refine ⟨a, sigR hc.sig (FiniteAdeleRing (𝓞 F) F) a, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · apply GlobalTheory.Mem.Col2.PtExist.ad_ext
    intro w
    rw [map_mul, ha, ha', map_one]
    split_ifs with hw hw'
    · rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    · rw [← map_mul, star_inv₀, inv_mul_cancel₀ (star_ne_zero.2 hc0), map_one]
    · rw [mul_one]
  · apply mem_RInt_of_valued_le_one
    intro P
    rw [ha]
    split_ifs with hw hw'
    · exact valued_inv_algebraMap_le_one_of_not_mem P _ (fun h => false_of_mem_of_conj_mem_of_isCoprime hcp P (hmem hw) h)
    · rw [hst]
      exact valued_algebraMap_int_le_one' P π
    · rw [map_one]
  · apply mem_RInt_of_valued_le_one
    intro P
    rw [ha']
    split_ifs with hw hw'
    · exact valued_algebraMap_int_le_one' P _
    · rw [star_inv₀, hst]
      exact valued_inv_algebraMap_le_one_of_not_mem P π (fun h => false_of_mem_of_conj_mem_of_isCoprime hcp P h ((mem_conjP P π).1 (hmem hw')))
    · rw [map_one]
  · intro P hP
    rw [ha', if_pos hP]
  · intro w hw
    rw [ha]
    split_ifs with h2 h3
    · exact absurd (Ideal.mul_mem_right _ _ (hmem h2)) hw
    · exact absurd (Ideal.mul_mem_left _ _ ((mem_conjP w π).1 (hmem h3))) hw
    · rfl

def stdPt (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : DecoF E n ∅ ∅ ∅ :=
  ⟨(⟨⟨stdLat E n, fun _ _ => 0, fun _ _ _ => 0⟩, stdLat_lattice, stdLat_unimodular,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim⟩, fun _ => 1), fun P => (Finset.notMem_empty _ P.2).elim⟩

theorem exists_base (hc : Formalism.BasicNotions.CMData F E) {π : 𝓞 E} {T : ℕ} (hT : T ≠ 0) (hπ : π * cO E π = T)
    (hcp : IsCoprime π (cO E π)) (n : ℕ) :
    ∃ k : GL (Fin n) (AfE F E), (∃ p : DecoF E n ∅ ∅ ∅, IsPtOf hc k p ∧ p.deco.1.N = stdLat E n) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) k = 1) ∧
      ∀ (P : divs π) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹).1 r j))
        (if j = r then Ideal.Quotient.mk P.1.asIdeal (cO E π) else 0) := by
  classical
  have hT0 : ((T : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have h0 : π ≠ 0 := fun h => hT0 (by rw [← hπ, h, zero_mul])
  have h1 : cO E π ≠ 0 := fun h => hT0 (by rw [← hπ, h, mul_zero])
  obtain ⟨a, a', haa, hσ, hai, hai', hP, hw⟩ := exists_unit hc h0 h1 hcp
  let d : Fin n → AfE F E := fun i => if i.1 + 1 = n then a else 1
  let d' : Fin n → AfE F E := fun i => if i.1 + 1 = n then a' else 1
  have hd : ∀ i, d' i * d i = 1 := fun i => by
    simp only [d, d']
    split_ifs
    · exact haa
    · exact mul_one 1
  have hd' : ∀ i, d i * d' i = 1 := fun i => by rw [mul_comm]; exact hd i
  have hdi : ∀ i, d i ∈ RInt F E := fun i => by
    simp only [d]
    split_ifs
    · exact hai
    · exact one_mem _
  have hdi' : ∀ i, d' i ∈ RInt F E := fun i => by
    simp only [d']
    split_ifs
    · exact hai'
    · exact one_mem _
  let k : GL (Fin n) (AfE F E) := ⟨Matrix.diagonal d, Matrix.diagonal d',
    by rw [Matrix.diagonal_mul_diagonal]; simp only [hd']; exact Matrix.diagonal_one,
    by rw [Matrix.diagonal_mul_diagonal]; simp only [hd]; exact Matrix.diagonal_one⟩
  have hk : ((k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = Matrix.diagonal d := rfl
  have hk' : ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = Matrix.diagonal d' := rfl
  refine ⟨k, ⟨stdPt E n, ?_, rfl⟩, ?_, ?_⟩
  · constructor
    · apply (GlobalTheory.Mem.Col2.PtExist.mem_uad_iff k).2
      unfold Formalism.UG.cT
      rw [hk, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      simp only [d]
      split_ifs
      · rw [hσ, haa]
      · rw [map_one, one_mul]
    · intro x
      unfold Formalism.L2.Herm.hatL
      change x ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (Formalism.L2.Col.stdLat E n) ↔ _
      rw [Formalism.L2.Col.mem_latS_std, Formalism.L2.Col.mem_latS_std, hk']
      constructor
      · intro h i
        rw [Matrix.mulVec_diagonal]
        exact mul_mem (hdi' i) (h i)
      · intro h i
        have := mul_mem (hdi i) (h i)
        rwa [Matrix.mulVec_diagonal, ← mul_assoc, hd' i, one_mul] at this
    all_goals intro P; exact (Finset.notMem_empty _ P.2).elim
  · intro v hv
    have hpa : prV (E := E) v a = 1 := by
      have h := ((GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v (a - 1)).1).2 (fun w hwv => by
        have hnot : π * cO E π ∉ w.asIdeal := by
          intro hmw
          apply hv
          rw [← hwv]
          change algebraMap (𝓞 F) (𝓞 E) (T : 𝓞 F) ∈ w.asIdeal
          rw [map_natCast, ← hπ]
          exact hmw
        rw [map_sub, hw w hnot, map_one, sub_self])
      rwa [map_sub, map_one, sub_eq_zero] at h
    apply Units.ext
    rw [Units.val_one]
    change (Matrix.diagonal d).map (prV (E := E) v) = 1
    rw [Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [d]
    split_ifs
    · exact hpa
    · exact map_one _
  · intro P r j hr
    rw [hk']
    unfold HasRes
    by_cases hj : j = r
    · subst hj
      rw [Matrix.diagonal_apply_eq, if_pos rfl]
      simp only [d', if_pos hr]
      rw [hP P.1 P.2]
      exact ⟨cO E π, rfl, by rw [sub_self, map_zero]; exact zero_lt_one⟩
    · rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), if_neg hj, map_zero]
      exact ⟨0, map_zero _, by rw [map_zero, map_zero, sub_self, map_zero]; exact zero_lt_one⟩

end General

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem exists_kStd : ∀ {B : Base} (X : PreX B.toPre), (B.primes X).Ok → ∀ (u : B.Word) (n : ℕ), ∃ k : GA B n, (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) ∧ (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) ∧ ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B n).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) := by
  intro B X hX u n
  exact exists_base B.sp.cm (π := X.piT u) (T := B.T u) (hX.T_prime u).ne_zero (hX.piT_norm u) (hX.piT_cop u) n

end GlobalTheory.Mem.Col2.BasePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermEqExtraTied
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ExtraTie

open Formalism.L2.Herm

theorem errX_eq {D : D7} (X : FullTiedS D) (H : ColsHermS D) (hX : X.cols = H) (e : ErrX D)
    (h1 : e.piG = (H.levelZeroCompatibility D.u₀).piG) (h2 : ∀ u, e.piT u = (H.atT u).piU)
    (h3 : ∀ u v, e.vPl u v = (H.base.vT u v).1) : e = toErrXS X := by
  subst hX
  obtain ⟨piG, piG_K, piG_norm, piT, piT_K, piT_norm, piT_cong, vPl, vPl_inj, norm_mem_place_ideal⟩ := e
  have e1 : piG = (X.levelZeroCompatibility D.u₀).piG := h1
  have e2 : piT = fun u => (X.atT u).piU := funext h2
  have e3 : vPl = fun u v => (X.base.vT u v).1 := funext fun u => funext (h3 u)
  subst e1 e2 e3
  rfl

end GlobalTheory.Mem.Col2.TC.ExtraTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCoefficientCompatibilityStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_coefficient_compatibility : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La), LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) c' (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))) := by
  first | exact @GlobalTheory.LevelActAnyField.actLev_of_levIs | exact GlobalTheory.LevelActAnyField.actLev_of_levIs | (intros; apply GlobalTheory.LevelActAnyField.actLev_of_levIs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeKeepsChartStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.move_down_level_prime_keeps_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → chOf ((I.fm l u a).dn i v c.1 g) = β := by
  first | exact @GlobalTheory.Mem.Col2.TC.dn_keeps_chart | exact GlobalTheory.Mem.Col2.TC.dn_keeps_chart | (intros; apply GlobalTheory.Mem.Col2.TC.dn_keeps_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAboveStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeProjection_zero_integral_iff_components_above : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (prV (E := E) v z = 0 ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → adAt F w z = 0) ∧ (prV (E := E) v z ∈ intV E v ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → Valued.v (adAt F w z) ≤ 1) := by
  first | exact @GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff | exact GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff | (intros; apply GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff <;> assumption)
end

