import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3167

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MultiplierIsUnit
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes GlobalTheory.LKGeo.MultScale
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

namespace UpperTheory.MultiplicativeUnitDivisibility

variable {p : ℕ} [Fact p.Prime]

private theorem exists_dvd_EFA (D : Datum p) (d : ℤ) (hd : ∀ x y : D.La, d ∣ D.EF x y)
    {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) :
    ∃ c : AfP p, IsIntAf c ∧ EFA D v w = (d : AfP p) * c := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, x, ha, rfl⟩ := hv
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a', x', ha', rfl⟩ := hw
      obtain ⟨k, hk⟩ := hd x x'
      refine ⟨a * a' * (k : AfP p), isIntAf_mul (isIntAf_mul ha ha') (isIntAf_intCast k), ?_⟩
      rw [EFA_tmul, hk]
      push_cast
      ring
    | zero => exact ⟨0, isIntAf_zero, by simp⟩
    | add u u' _ _ h h' =>
      obtain ⟨c, hc, e⟩ := h
      obtain ⟨c', hc', e'⟩ := h'
      exact ⟨c + c', isIntAf_add hc hc', by rw [map_add, e, e', mul_add]⟩
    | neg u _ h =>
      obtain ⟨c, hc, e⟩ := h
      exact ⟨-c, isIntAf_neg hc, by rw [map_neg, e, mul_neg]⟩
  | zero => exact ⟨0, isIntAf_zero, by simp⟩
  | add u u' _ _ h h' =>
    obtain ⟨c, hc, e⟩ := h
    obtain ⟨c', hc', e'⟩ := h'
    exact ⟨c + c', isIntAf_add hc hc', by rw [map_add, LinearMap.add_apply, e, e', mul_add]⟩
  | neg u _ h =>
    obtain ⟨c, hc, e⟩ := h
    exact ⟨-c, isIntAf_neg hc, by rw [map_neg, LinearMap.neg_apply, e, mul_neg]⟩

private theorem exists_ne (D : Datum p) : ∃ x y : D.La, D.EF x y ≠ 0 := by
  have hF : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  have hr : 0 < Module.finrank ℤ D.La := by
    rw [D.rankLa]
    exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) hF
  haveI := Module.nontrivial_of_finrank_pos hr
  obtain ⟨x, hx⟩ := _root_.exists_ne (0 : D.La)
  have hne : D.EF x ≠ 0 := by
    intro h
    apply hx
    apply D.nondeg
    rw [h, map_zero]
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp hne
  exact ⟨x, y, by simpa using hy⟩

private theorem isUnit_intCast {d : ℤ} (hd : d ≠ 0) : IsUnit (d : AfP p) := by
  have h : IsUnit (d : ℚ) := (Int.cast_ne_zero.mpr hd).isUnit
  simpa using h.map (algebraMap ℚ (AfP p))

private theorem isIntAf_sim {D : Datum p} {G : HTGroup p} (L : Link D G) (g : G.GAf)
    (hg : ∀ v ∈ LaHat D, L.actG g v ∈ LaHat D) : IsIntAf ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) := by
  let S : Set ℤ := {z | ∃ x y : D.La, D.EF x y = z}
  obtain ⟨d, hdI⟩ := (IsPrincipalIdealRing.principal (Ideal.span S)).principal
  have hdvd : ∀ x y : D.La, d ∣ D.EF x y := by
    intro x y
    have hm : D.EF x y ∈ Ideal.span S := Ideal.subset_span ⟨x, y, rfl⟩
    rw [hdI] at hm
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
    exact ⟨a, by rw [← ha, smul_eq_mul, mul_comm]⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, hxy⟩ := exists_ne D
    apply hxy
    obtain ⟨k, hk⟩ := hdvd x y
    rw [hk, zero_mul]
  have key : ∀ z ∈ Ideal.span S, ∃ c : AfP p, IsIntAf c ∧
      ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) * (z : AfP p) = (d : AfP p) * c := by
    intro z hz
    change z ∈ Submodule.span ℤ S at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, y, rfl⟩ := hz
      have h1 := EFA_actG L g (inAf D x) (inAf D y)
      rw [EFA_inAf] at h1
      rw [← h1]
      exact exists_dvd_EFA D d hdvd (hg _ (inAf_mem D x)) (hg _ (inAf_mem D y))
    | zero => exact ⟨0, isIntAf_zero, by simp⟩
    | add a b _ _ h1 h2 =>
      obtain ⟨c1, h1i, h1e⟩ := h1
      obtain ⟨c2, h2i, h2e⟩ := h2
      refine ⟨c1 + c2, isIntAf_add h1i h2i, ?_⟩
      rw [Int.cast_add, mul_add, h1e, h2e, mul_add]
    | smul a b _ h =>
      obtain ⟨c, hi, he⟩ := h
      refine ⟨a * c, isIntAf_mul (isIntAf_intCast a) hi, ?_⟩
      rw [smul_eq_mul, Int.cast_mul, mul_left_comm, he]
      ring
  obtain ⟨c, hc, hce⟩ := key d (by rw [hdI]; exact Submodule.mem_span_singleton_self d)
  have hsc : ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) = c :=
    (isUnit_intCast (p := p) hd0).mul_left_cancel (by rw [mul_comm]; exact hce)
  rw [hsc]
  exact hc

private theorem pow_dvd_of_isIntAf {q k c c' : ℕ} (hq : q.Prime) (hqp : q ≠ p) {t : AfP p} (ht : IsIntAf t)
    (h : (c : AfP p) = c' * t) (hd : q ^ k ∣ c') : q ^ k ∣ c := by
  obtain ⟨m, rfl⟩ := hd
  have hm : IsIntAf ((m : AfP p) * t) := by
    have hmi := isIntAf_intCast (p := p) (m : ℤ)
    rw [Int.cast_natCast] at hmi
    exact isIntAf_mul hmi ht
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  let v0 : HeightOneSpectrum ℤ :=
    ⟨Ideal.span {(q : ℤ)}, (Ideal.span_singleton_prime hq0).mpr hqz,
      by rw [Ne, Ideal.span_singleton_eq_bot]; exact hq0⟩
  have hv0p : v0.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro heq
    have hmem : (q : ℤ) ∈ Ideal.span {(p : ℤ)} := heq ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton] at hmem
    have hpq : p ∣ q := Int.natCast_dvd_natCast.mp hmem
    exact hqp ((Nat.prime_dvd_prime_iff_eq Fact.out hq).mp hpq).symm
  let v : AwayP p := ⟨v0, hv0p⟩
  have hev : (AfP.eval v) (c : AfP p) =
      (q : HeightOneSpectrum.adicCompletion ℚ v0) ^ k * (AfP.eval v) ((m : AfP p) * t) := by
    rw [h, Nat.cast_mul, Nat.cast_pow, mul_assoc, map_mul, map_pow, map_natCast]
  have hval : ∀ n : ℕ, Valued.v (n : HeightOneSpectrum.adicCompletion ℚ v0) = v0.intValuation (n : ℤ) := by
    intro n
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v0 (n : ℤ)
    rw [HeightOneSpectrum.valuation_of_algebraMap] at h1
    rw [← h1]
    congr 1
    simp
  have hs : Valued.v ((AfP.eval v) ((m : AfP p) * t)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers ℤ ℚ v0).mp (hm v)
  have hle : v0.intValuation (c : ℤ) ≤ WithZero.exp (-(k : ℤ)) := by
    have hc := hval c
    rw [map_natCast] at hev
    rw [← hc, hev, map_mul, map_pow, hval q, HeightOneSpectrum.intValuation_singleton v0 hq0 rfl]
    refine (mul_le_of_le_one_right' hs).trans (le_of_eq ?_)
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  rw [HeightOneSpectrum.intValuation_le_pow_iff_dvd] at hle
  change Ideal.span {(q : ℤ)} ^ k ∣ Ideal.span {(c : ℤ)} at hle
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd] at hle
  exact_mod_cast hle

private theorem dvd_of_isIntAf {c c' : ℕ} (hc' : c'.Coprime p) {t : AfP p} (ht : IsIntAf t)
    (h : (c : AfP p) = c' * t) : c' ∣ c := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd c c']
  intro q k hq hqk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hqp : q ≠ p := by
      rintro rfl
      have hqc : q ∣ c' := (dvd_pow_self q hk.ne').trans hqk
      exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqc hc') dvd_rfl)
    exact pow_dvd_of_isIntAf hq hqp ht h hqk

private theorem main : MultUnit := by
  intro p _ D G L
  refine ⟨?_, ?_⟩
  · intro u hu
    have hst : ∀ g ∈ L.KN 1, ∀ v ∈ LaHat D, L.actG g v ∈ LaHat D := by
      intro g hg v hv
      obtain ⟨w, hw, e⟩ := hg.1 v hv
      rw [e, one_smul]
      exact add_mem hv hw
    have h1 := isIntAf_sim L u (hst u hu)
    have h2 := isIntAf_sim L u⁻¹ (hst _ (inv_mem hu))
    refine ⟨((uSimR (AfP p) u⁻¹ : (AfP p)ˣ) : AfP p), h1, h2, ?_⟩
    have h3 : (uSimR (AfP p) u⁻¹ : (AfP p)ˣ) = ((u : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ := rfl
    rw [h3]
    exact Units.mul_inv _
  · intro c c' t t' hc hc' ht ht' htt h
    refine Nat.dvd_antisymm ?_ (dvd_of_isIntAf hc' ht h)
    refine dvd_of_isIntAf hc ht' ?_
    rw [h, mul_assoc, htt, mul_one]

end UpperTheory.MultiplicativeUnitDivisibility

theorem UpperTheory.multiplier_is_unit : MultUnit := UpperTheory.MultiplicativeUnitDivisibility.main
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientInvariantOfTraceUnitCrt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

private theorem isIntAf_one' {p : ℕ} [Fact p.Prime] : IsIntAf (1 : AfP p) := fun v => by
  rw [map_one]; exact one_mem _

private theorem inAf_mem' {p : ℕ} [Fact p.Prime] {D : Datum p} (y : D.La) : inAf D y ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, y, isIntAf_one', rfl⟩

set_option maxHeartbeats 200000 in
theorem UpperTheory.quotient_invariant_of_trace_unit_crt :
    NumEx → QComp → QIso → ClsEx → TrEta → TrUnit → CongCRT → BaseInv := by
  intro hNumEx hQComp hQIso hClsEx hTrEta hTrUnit hCRT p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N' N t c a hN't hNum C' C u hu W
  have hNpos : 0 < (N : ℕ) := by have := N.2.1; omega
  have hN'pos : 0 < (N' : ℕ) := by have := N'.2.1; omega
  have hNum' := (hNumEx p D E gb w q r 𝔴 𝔫 S (N : ℕ) hNpos).2 c a t hNum
  obtain ⟨hNc, hGen⟩ := hNum
  obtain ⟨-, hGen'⟩ := hNum'
  rw [← hN't] at hGen'
  have hN'c : (N' : ℕ) = S.N₀ * (c * t) := by rw [hN't, hNc, _root_.mul_assoc]
  have h3 : 3 ≤ S.N₀ := S.std.three
  have hcq : S.N₀.Coprime q := S.std.cop
  have hu1 := ((hLev u).mp hu).1
  have hIu : Integ L u := integ_of_mem hu1
  have hCRTu := hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu
  have hC := hCRTu.1.mp (by have h1 := ((hLev u).mp hu).2; rwa [S.lev] at h1)
  have hEta : ∀ y : D.La, (T.M N').univ.eta ((c * t) • y) ≫ W.ψ = W.o.eta (c • y) := by
    intro y
    obtain ⟨v, hv, ev⟩ := hC.1 _ (inAf_mem' y)
    exact hTrEta p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans S.N₀ (c * t) c hN'c hNc y y ⟨v, hv, ev⟩
  obtain ⟨hIso, hLB⟩ := hTrUnit p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans hu1
  obtain ⟨qC, hqC⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨n', hn'⟩ := hQIso q _ _ _ _ _ _ _ _ c (c * t) _ _ _ _ (T.M N').univ W.o S.Y.univ _ W.ψ hIso W.trans.1
    W.trans.2.1 hLB hEta qC
  have hov : (W.π ≫ C.j) ≫ S.Y.s = (T.M N').s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, C.ov, reassoc_of% W.ov]
  have hlv : ∀ y : D.La, ((T.M N').univ.eta ((algebraMap (𝓞 D.F) D.O) (↑t * a) • y)).left ≫ n'.φ =
      (W.π ≫ C.j) ≫ (S.Y.lv y).left := by
    intro y
    have hsm : (algebraMap (𝓞 D.F) D.O (↑t * a)) • y = t • ((algebraMap (𝓞 D.F) D.O) a • y) := by
      rw [map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
    obtain ⟨v₂, hv₂, e₂⟩ := (hCRTu.2 a N hNpos N.2.2 hGen).mp hC.2 y
    have hTE := hTrEta p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans N t 1 hN't
      (_root_.mul_one _).symm _ _ ⟨v₂, hv₂, e₂⟩
    rw [one_smul] at hTE
    rw [hsm, hn', hqC, ← Category.assoc, ← Over.comp_left, hTE, ← Category.assoc]
    erw [W.φ.eta]
    rw [Category.assoc, C.lv, Category.assoc]
  obtain ⟨-, huq⟩ := hClsEx q _ _ _ S.b gb _ S.mat _ _ _ _ _ hN'c hN'pos h3 hcq hGen' S.Y _ _ (T.M N').univ
  obtain ⟨hj, hm⟩ := huq ⟨W.π ≫ C.j, hov, n', hlv⟩ C'
  refine ⟨hj, ?_⟩
  calc Over.Hom.left W.ψ ≫ W.φ.φ ≫ C.m.φ = n'.φ := by rw [hn', hqC]
    _ = C'.m.φ := hm
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientLevelOfLatticeGeneration
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.LevelActionGenerator

variable {X : Scheme.{0}}

private theorem pb_mul {A B : Over X} [GrpObj A] [GrpObj B] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B (𝟙 X) φ) (f : A ⟶ B) (hf : f.left = φ) {T : Over X} (x y : T ⟶ A) :
    (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  let e : Over.mk (T.hom ≫ 𝟙 X) ≅ T := Over.isoMk (Iso.refl _) (by simp)
  have he : e.hom.left = 𝟙 _ := rfl
  have key := h.2 T x y (e.hom ≫ x ≫ f) (e.hom ≫ y ≫ f)
    (by rw [Over.comp_left, Over.comp_left, he, Category.id_comp, hf])
    (by rw [Over.comp_left, Over.comp_left, he, Category.id_comp, hf])
  rw [← MonObj.comp_mul, Over.comp_left, he, Category.id_comp] at key
  apply Over.OverMorphism.ext
  rw [key, Over.comp_left, hf]

private theorem pb_one {A B : Over X} [GrpObj A] [GrpObj B] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B (𝟙 X) φ) (f : A ⟶ B) (hf : f.left = φ) {T : Over X} :
    (1 : T ⟶ A) ≫ f = 1 := by
  have h1 := pb_mul h f hf (1 : T ⟶ A) 1
  rw [_root_.mul_one] at h1
  simpa using h1

private theorem act_nat {O : Type} [Ring O] {A : Over X} [GrpObj A] [IsCommMonObj A] (act : OActN O A) {T : Over X}
    (u : T ⟶ A) (m : ℕ) : u ≫ act.act (m : O) = u ^ m := by
  induction m with
  | zero =>
    have h0 : act.act (0 : O) = 1 := by
      have := act.add 0 0
      rw [add_zero] at this
      simpa using this
    rw [Nat.cast_zero, h0, pow_zero, MonObj.comp_one]
  | succ m ih =>
    rw [Nat.cast_succ, act.add, act.one, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

private theorem gen_mem {A : Type} [CommRing A] {a : A} {N : ℕ} {𝔞 : Ideal A} (h : IsGen a N 𝔞) : (N : A) ∈ 𝔞 := by
  have h' : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)} := h
  have hm : (N : A) ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 := by
    rw [h']
    exact Ideal.subset_span (Set.mem_singleton _)
  exact (Ideal.mul_le_right (I := Ideal.span {a} ⊔ Ideal.span {(N : A)}) (J := 𝔞)) hm

end UpperTheory.LevelActionGenerator

open UpperTheory.LevelActionGenerator in
theorem UpperTheory.quotient_level_of_lattice_generation :
    LatGen → QLev := by
  intro hLat q _ D R R' _ _ _ b gb N N₀ c a 𝔞 hN hgen X s s₀ o o₀ n
  have hw : n.φ ≫ o₀.A.hom = o.A.hom := by simpa using n.cart.1.w
  haveI : IsIso n.φ := n.cart.1.isIso_fst_of_isIso
  let f : o.A ⟶ o₀.A := Over.homMk n.φ hw
  let g : o₀.A ⟶ o.A := Over.homMk (inv n.φ) (by rw [IsIso.inv_comp_eq, hw])
  have hfl : f.left = n.φ := rfl
  have hfg : f ≫ g = 𝟙 _ := by
    apply Over.OverMorphism.ext
    simp [f, g]
  have hgf : g ≫ f = 𝟙 _ := by
    apply Over.OverMorphism.ext
    simp [f, g]
  have hinj : ∀ {T : Over X} (u v : T ⟶ o.A), u ≫ f = v ≫ f → u = v := by
    intro T u v huv
    have := congrArg (· ≫ g) huv
    simpa [Category.assoc, hfg] using this
  have hmul : ∀ {T : Over X} (u v : T ⟶ o.A), (u * v) ≫ f = (u ≫ f) * (v ≫ f) :=
    fun u v => pb_mul n.cart f hfl u v
  have hone : ∀ {T : Over X}, (1 : T ⟶ o.A) ≫ f = 1 := pb_one n.cart f hfl
  have hone' : ∀ {T : Over X}, (1 : T ⟶ o₀.A) ≫ g = 1 := by
    intro T
    apply hinj
    rw [Category.assoc, hgf, Category.comp_id, hone]
  have hact : ∀ c' : D.O, o.act.act c' ≫ f = f ≫ o₀.act.act c' := by
    intro c'
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    exact n.act c'
  have e_add : ∀ u v : D.La, o.eta (u + v) = o.eta u * o.eta v := fun u v => o.eta_add u v
  have e_lin : ∀ (c' : D.O) (u : D.La), o.eta (c' • u) = o.eta u ≫ o.act.act c' :=
    fun c' u => o.eta_lin c' u
  have e_ker : ∀ u : D.La, o.eta (N • u) = 1 := fun u => o.eta_ker u
  obtain ⟨hL1, hL2⟩ := hLat q D a N 𝔞 hN hgen
  refine ⟨fun y => o.eta (algebraMap (𝓞 D.F) D.O a • y) ≫ f, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y z
    simp only
    rw [smul_add, e_add, hmul]
  · intro c' y
    simp only
    have hcomm : algebraMap (𝓞 D.F) D.O a • (c' • y) = c' • (algebraMap (𝓞 D.F) D.O a • y) := by
      rw [smul_smul, smul_smul, Algebra.commutes]
    rw [hcomm, e_lin, Category.assoc, hact, Category.assoc]
  · intro y hy
    obtain ⟨z, hz⟩ := (hL1 y).2 hy
    simp only
    rw [hz, e_ker, hone]
  · intro k _ _ x
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := by
      simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    obtain ⟨I, hI⟩ := o.geom k x _ hβ
    have hI' : ∀ y : D.La, toUnit (Over.mk x) ≫ o.eta y = I.ev N y := fun y => hI y
    have I_add : ∀ u v : D.La, I.ev N (u + v) = I.ev N u * I.ev N v := fun u v => I.add N u v
    have I_lin : ∀ (c' : D.O) (u : D.La), I.ev N (c' • u) = I.ev N u ≫ o.act.act c' :=
      fun c' u => I.lin N c' u
    have I_ker : ∀ u : D.La, I.ev N u = 1 ↔ ∃ v : D.La, u = N • v := fun u => I.ker N hN u
    have I_onto : ∀ r : Over.mk x ⟶ o.A, r ^ N = 1 ↔ ∃ u : D.La, I.ev N u = r :=
      fun r => I.onto N hN r
    constructor
    · intro y hy
      simp only at hy
      rw [← Category.assoc, ← hone] at hy
      have h1 := hinj _ _ hy
      rw [hI'] at h1
      obtain ⟨z, hz⟩ := (I_ker _).1 h1
      exact (hL1 y).1 ⟨z, hz⟩
    · intro g₀ hg₀
      have hg'act : ∀ c' : D.O, (g₀ ≫ g) ≫ o.act.act c' = (g₀ ≫ o₀.act.act c') ≫ g := by
        intro c'
        apply hinj
        simp only [Category.assoc, hact, reassoc_of% hgf, hgf, Category.comp_id]
      have hkill : ∀ c' ∈ 𝔞, (g₀ ≫ g) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c') = 1 := by
        intro c' hc'
        rw [hg'act, hg₀ c' (by rwa [pow_one]), hone']
      have hpow : (g₀ ≫ g) ^ N = 1 := by
        have hn := act_nat o.act (g₀ ≫ g) N
        have hc : ((N : ℕ) : D.toG.O) = algebraMap (𝓞 D.F) D.O (N : 𝓞 D.F) := (map_natCast _ N).symm
        rw [hc] at hn
        rw [← hn]
        exact hkill _ (gen_mem hgen)
      obtain ⟨x', hx'⟩ := (I_onto (g₀ ≫ g)).1 hpow
      have hcond : ∀ c' ∈ 𝔞, ∃ z : D.La, algebraMap (𝓞 D.F) D.O c' • x' = N • z := by
        intro c' hc'
        apply (I_ker _).1
        rw [I_lin, hx']
        exact hkill c' hc'
      obtain ⟨y, z, hyz⟩ := hL2 x' hcond
      refine ⟨y, ?_⟩
      have hyI : toUnit (Over.mk x) ≫ o.eta (algebraMap (𝓞 D.F) D.O a • y) = g₀ ≫ g := by
        rw [hI', ← hx', hyz, I_add, (I_ker (N • z)).2 ⟨z, rfl⟩, _root_.mul_one]
      simp only
      rw [← Category.assoc, hyI, Category.assoc, hgf, Category.comp_id]
  · intro y
    rfl
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientSeparatedOfTraceUnitCrt
section
open UpperTheory.Gal.Int.Geo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo

private theorem inAf_mem {p : ℕ} [Fact p.Prime] (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

theorem UpperTheory.quotient_separated_of_trace_unit_crt :
    GPull → QComp → QIso → QUniq → TrEta → TrEtaPt → TrUnit → CongCRT → BaseSep := by
  intro hGP hQC hQI hQU hTE hTP hTU hCRT
  intro p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNum C u hu W Ω _ _ z hz
  have huN : L.CongOne S.N₀ u ∧ L.CongOne S.N₀ u⁻¹ := hu
  have hu1 : u ∈ L.KN 1 := KN_anti (one_dvd _) hu
  have hInt : Integ L u := integ_of_mem hu1
  rw [hLev]
  refine ⟨hu1, ?_⟩
  rw [S.lev]
  obtain ⟨hcrt1, hcrt2⟩ := hCRT p D G L q r S.N₀ S.𝔞 S.std.cop S.upow u hInt
  rw [hcrt1]
  refine ⟨huN.1, ?_⟩
  have hNpos : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  rw [hcrt2 a N hNpos N.2.2 hNum.2]
  intro y
  set x := (algebraMap (𝓞 D.F) D.O a) • y with hx
  refine (hTP p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans Ω z x).2 rfl x ?_
  have ht : (toUnit (Over.mk z)).left = z := by
    simpa using Over.w (toUnit (Over.mk z))
  obtain ⟨oz, ⟨mz⟩⟩ := hGP _ _ gb (N : ℕ) (T.M N).X (Sp Ω) (T.M N).s z (T.M N).univ
  obtain ⟨nW, hnW⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨hiso, hlb⟩ := hTU p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans hu1
  have heta : ∀ y' : D.La, (T.M N).univ.eta (c • y') ≫ W.ψ = W.o.eta (c • y') := by
    intro y'
    refine hTE p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans S.N₀ c c hNum.1 hNum.1
      y' y' ?_
    exact huN.1 _ (inAf_mem D y')
  obtain ⟨nI, hnI⟩ := hQI q (datAt S.atq S.sp) (Ow w) E S.b gb N N S.N₀ c c _ _ _ _ (T.M N).univ W.o S.Y.univ _ W.ψ hiso W.trans.1
    W.trans.2.1 hlb heta nW
  obtain ⟨nA, hnA⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ oz z mz C.m
  obtain ⟨nB, hnB⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ (W.π ≫ C.j) (𝟙 _)).2.2.2
    _ _ oz z mz nI
  have hfeq : z ≫ W.π ≫ C.j = z ≫ C.j := hz
  have hAB : mz.φ ≫ Over.Hom.left W.ψ ≫ W.φ.φ ≫ C.m.φ = mz.φ ≫ C.m.φ := by
    generalize hF : z ≫ W.π ≫ C.j = F at nB hnB
    have hF' : F = z ≫ C.j := hF.symm.trans hfeq
    subst hF'
    have h := hQU q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c S.std.three S.std.cop _ _ _ _ _ _ _ nB nA
    rw [hnB, hnI, hnW, hnA] at h
    exact h
  apply Over.OverMorphism.ext
  apply nW.cart.1.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    rw [hnW, reassoc_of% (W.φ.eta x)]
    have hl := C.lv y
    have hr : Over.Hom.left ((T.M N).univ.eta x) ≫ C.m.φ = C.j ≫ Over.Hom.left (S.Y.lv y) := hl
    have hz' := mz.eta x
    rw [ht]
    rw [← reassoc_of% hz', hAB, reassoc_of% hz', hr, reassoc_of% hfeq]
  · simp only [Over.comp_left, Category.assoc, Over.w]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.StandardDatumExists
section
open UpperTheory.Gal.Int.Geo

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen in
theorem UpperTheory.standard_datum_exists :
    StdEx := by
  intro p _ D ha E _ _ e
  let φ : 𝓞 D.F →+* E := (e : D.F →+* E).comp (algebraMap (𝓞 D.F) D.F)
  have key : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]
    ring
  have hroot : φ D.ω ^ 2 - (D.tr : E) * φ D.ω + (D.nm : E) = 0 := by
    simpa using congrArg φ key
  have hsub : Subsingleton (Fin D.toG.a) := by
    have h : D.toG.a = 1 := ha
    rw [h]
    infer_instance
  exact ⟨{ ρ := φ D.ω
           ρ_root := hroot
           t := fun _ => φ
           t_ω := fun _ => rfl
           comax := fun i j hij => (hij (Subsingleton.elim i j)).elim }, rfl, fun _ _ => rfl⟩
end

