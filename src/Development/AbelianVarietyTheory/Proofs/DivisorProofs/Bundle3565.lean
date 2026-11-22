import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3553
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3285
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3556
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3530
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpecStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVarietyEndCharpoly_spec : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A), IsCharpoly f (charpoly f) ∧ ∀ P, IsCharpoly f P → P = charpoly f := by
  first | (exact @GlobalTheory.AV.AbVar.charpoly_spec) | (exact GlobalTheory.AV.AbVar.charpoly_spec) | (intros; apply GlobalTheory.AV.AbVar.charpoly_spec  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicNormNefPartialSums
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtGen

open GlobalTheory.LineNorm GlobalTheory.Cartier

theorem nefOver_of_icls {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {d : ℕ} (hX : IsArithVar p d)
    {L A B : HermLB p} {m : ℕ} (hm : 0 < m) (h : m • L.icls = A.icls + B.icls) {l : ℕ} (hA : NefOver A l)
    (hB : NefOver B l) : NefOver L l := by
  intro Z i _ _ κ _ _ _ _ hd
  have : Module.Finite ℤ k := hX.finite
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  have hproj : IsProjOver (strHom κ Z) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom κ Z ≫ spMap (Int.castRingHom κ) =
        i ≫ p ≫ spMap (Int.castRingHom k) := specZIsTerminal.hom_ext _ _
    have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by
      rw [e]; infer_instance
    have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
    exact ProperCurve.isProjOver_of_isProper _ hd
  let F₀ : HermLB.IsomClass p → ℤ :=
    Quotient.lift (s := HermLB.isometrySetoid p) (fun L => topSelfIntersection κ (L.B.pull i) 1) fun L L' e => by
      have ⟨w, hw, _⟩ := HermLB.Isometric.pull e i rfl
      exact interNum_congr_lbIso κ _ (fun _ => (L.restr i).isLB) (fun _ => (L'.restr i).isLB) fun _ => ⟨w, hw⟩
  let G : HermLB.IsomClass p →+ ℤ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨L'⟩
    exact HtTensCurve.topSelf_one_pull_tens hproj hd i L.isLB L'.isLB)
  have e := congrArg G h
  rw [map_nsmul, map_add, nsmul_eq_mul] at e
  have h₁ : 0 ≤ G A.icls := hA Z i κ hd
  have h₂ : 0 ≤ G B.icls := hB Z i κ hd
  change 0 ≤ G L.icls
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hm : (0 : ℤ) < m)).1 (e ▸ add_nonneg h₁ h₂)

theorem nefOver_of_pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {d : ℕ} (hX : IsArithVar p d)
    {L : HermLB p} {m : ℕ} (hm : 0 < m) {l : ℕ} (h : NefOver (L.pow m) l) : NefOver L l :=
  nefOver_of_icls hX (m := m + m) (by omega) (by rw [HermLB.icls_pow, add_nsmul]) h h

theorem residueCharacteristic_eq {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) {l : ℕ}
    (hl : l.Prime) (h : (l : 𝓞 F) ∈ v.asIdeal) : resP v = l := by
  obtain ⟨hp, -⟩ := ioOf_spec F v e
  refine (Nat.prime_dvd_prime_iff_eq hp hl).1 (ringChar.dvd ?_)
  rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 h

section Flags

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {lv : Level H} {Xo : Moduli Dw lv} {c : Coeff lv} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {ε : F ≃+* c.F} (C : GlobalTheory.ShFam.FlagCpt Z ε)

theorem symLog_eq {b : ℕ → Bool} {l : ℕ} (hl : l.Prime) (hb : b l = true) (σ : E →+* ℂ) (i : Fin (Dw.mult σ))
    (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt C.Y) (h : (l : 𝓞 F) ∈ v.asIdeal) :
    symLog C b (.inl (σ, i)) v e y = stepLog Z.t (C.π ≫ GlobalTheory.Toroidal.genι Z) (fun y => (fr C y).v σ) l i v e y +
      (if σ (H.rt : E) = H.rt0 then vDiff E l else 0) * Real.log (e.w l) := by
  obtain rfl := residueCharacteristic_eq e hl h
  rw [mixLog_eq (b := b) (by simp [hb])]
  have hl' : Real.log (resP v) ≠ 0 := (Real.log_pos (by exact_mod_cast hl.one_lt)).ne'
  simp only [symLog, mixLog, lnStep, dif_pos hl, dif_pos i.2, hb, true_and]
  split_ifs
  · field_simp
    ring
  · simp

theorem nefOver_step [IsLocallyNoetherian Z.X] (hX : Z.X.IsSeparated) (V : Cover C.Y) (ρ' : V.X ⟶ Z.X)
    (hρ : V.j ≫ ρ' = V.π ≫ C.π ≫ GlobalTheory.Toroidal.genι Z) {l : ℕ} [hl : Fact l.Prime] (hc : CharFam Z.t ρ' l 2)
    {b : ℕ → Bool} (hb : b l = true) (σ : E →+* ℂ) {k : ℕ} (hk : k ≤ Dw.mult σ) {L : HermLB V.p}
    {a : ∀ s : F →+* ℂ, Pts C.Y s → ℝ}
    (h : Norms V L (fun y => ((∏ i : Fin k, dg C y σ (Fin.castLE hk i) : C.Y.Fnˣ) : C.Y.Fn)) a
      fun v e y => -∑ i : Fin k, symLog C b (.inl (σ, (Fin.castLE hk i : ℕ))) v e y) : NefOver L l := by
  have h₁ := GlobalTheory.T.torsion_char_tangent_family E H Z.X Z.t hX F C.Y V ρ' _ hρ l hc _ _ _ _ (isFlagFrame_eig C σ) k hk
  have hm : 0 < Module.finrank ℚ E := Module.finrank_pos
  have h₂ := norms_pow F C.Y V _ _ _ _ (Module.finrank ℚ E) h
  refine nefOver_of_pow V.ar hm (GlobalTheory.T.nef_over_of_generated F C.Y V _ _ _ _ l h₂ (GlobalTheory.T.generic_over_power F C.Y V _ _ _ l _
    (-(k * if σ (H.rt : E) = H.rt0 then padicValNat l (discr E).natAbs else 0 : ℕ)) hl.out.ne_zero hm
    (fun v e y hv => ?_) h₁))
  simp only [symLog_eq C hl.out hb σ _ v e y hv, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : ((Module.finrank ℚ E : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  split_ifs
  · have h₃ : vDiff E l * Module.finrank ℚ E = padicValNat l (discr E).natAbs := div_mul_cancel₀ _ this
    rw [Int.cast_neg, Int.cast_natCast, Nat.cast_mul]
    linear_combination (-(k : ℝ) * Real.log (e.w l)) * h₃
  · simp

theorem norms_single {V : Cover C.Y} {L : HermLB V.p} {a : ∀ s : F →+* ℂ, Pts C.Y s → ℝ} (b : ℕ → Bool) (σ : E →+* ℂ)
    {k : ℕ} (hk : k < Dw.mult σ) (n : ℤ) {w : Sym E →₀ ℤ} (hw : w = Finsupp.single (b, none, .inl (σ, k)) n)
    (h : Norms V L (fun y => genAt (divOf C (expo Dw w)) y) a fun v e y => lgOf C w v e y) :
    ∃ a', Norms V L (fun y => ((dg C y σ ⟨k, hk⟩ ^ (-n) : C.Y.Fnˣ) : C.Y.Fn)) a'
      fun v e y => n * symLog C b (.inl (σ, k)) v e y := by
  have hP (y : C.Y.X) : ∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw w x = dg C y σ ⟨k, hk⟩ ^ n := by
    rw [Finset.prod_eq_single ⟨σ, ⟨k, hk⟩⟩ (fun x _ hx => by
      rw [hw, expo_single, if_neg (by simpa [letterOf, hk] using hx.symm), zpow_zero]) (by simp), hw, expo_single,
      if_pos (by simp [letterOf, hk])]
  have hu (y : C.Y.X) : UnitAt y (((dg C y σ ⟨k, hk⟩ ^ n) * (eqn (divOf C (expo Dw w)) y)⁻¹ : C.Y.Fnˣ) : C.Y.Fn) := by
    have h₁ : (divOf C (expo Dw w)).IsEqn y (∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw w x) :=
      isEqn_sum _ y fun x => ((fr_spec C y).2 x.1 x.2).zsmul _
    rw [hP] at h₁
    simpa [div_eq_mul_inv] using (Base.isEqn_eqn _ y).iff_unitAt.1 h₁
  refine ⟨_, (norms_mul_unit F C.Y V L _ _ _ _ (fun y => (hu y).inv) h).congr (fun y => ?_) (fun _ _ => rfl)
    fun v e y => ?_⟩
  · rw [← Units.val_inv_eq_inv_val, genAt, ← Units.val_mul]
    congr 1
    rw [mul_inv, inv_inv, mul_inv_cancel_right, zpow_neg]
  · rw [lgOf_eq_lgCopy, lgCopy_eq, hP, GlobalTheory.LineNorm.Neg.valAt_inv (hu _), map_inv₀, Real.log_inv, neg_add_cancel_left, hw]
    exact Finsupp.sum_single_index (h := fun (a : Sym E) (n : ℤ) => (n : ℝ) * symLog C a.1 a.2.2 v e y) (by simp)

end Flags

theorem prod_zpow_of_injective {α G : Type} [Fintype α] [CommGroup G] {k : ℕ} (e : Fin k → α) (he : Function.Injective e)
    (f : α → G) (n : α → ℤ) (s : ℤ) (h₀ : ∀ x, x ∉ Set.range e → n x = 0) (h₁ : ∀ i, n (e i) = s) :
    ∏ x, f x ^ n x = ∏ i, f (e i) ^ s :=
  (Fintype.prod_of_injective e he _ _ (fun x hx => by rw [h₀ x hx, zpow_zero]) fun i => by rw [h₁]).symm

end GlobalTheory.HtGen

open GlobalTheory.HtGen GlobalTheory.LineNorm in

theorem GlobalTheory.HtGen.exists_cover_nefOver_steps : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∃ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) ∧ ∀ (τ : D.what₂.Tau) (i : ℕ), i < O.N → NefOver (ArInt.comb M fun x => if x.1 = τ ∧ x.2.val < i then -1 else 0) l := by
  intro h2 hH D O hO hf A T H h c Q l hlQ hl
  have := Fact.mk hl
  obtain ⟨hX, hN, M₀, ρ', -, hρ⟩ := GlobalTheory.T.exists_normal_model_over_projective D.what₂.LL (O.Φ.C c).Y (𝓞 O.κ.c.F) (RingOfIntegers.mapRingEquiv O.κ.e)
    O.s.T.Z.X O.s.T.Z.s ((O.Φ.C c).π ≫ GlobalTheory.Toroidal.genι O.s.T.Z) O.s.T.Z.proj (by
      rw [← (O.Φ.C c).π_str]
      simp only [Category.assoc]
      rw [Limits.pullback.condition_assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl)
  let W := h.mdl Q c
  obtain ⟨V, a, g, ρ'', ha, e₁, e₂, e₃, e₄, hz, hζ, hs⟩ :=
    GlobalTheory.T.cover_refinement_exists _ _ _ O.s.T.Z.t _ _ M₀ ρ' W.V (l ^ 2) (pow_ne_zero _ hl.ne_zero)
  rw [hρ] at e₄
  have hc := GlobalTheory.T.torsion_split_normal_base _ _ _ O.s.T.Z.t V.X ρ'' l 2 V.normal hz hζ hs
  obtain ⟨M, hM⟩ : ∃ M : DV.Rt D.what₂.Tau O.N → HermLB V.p, ∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z)
      (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y) :=
    ⟨_, fun x => (norms_pull _ _ W.V V a ha g e₁ e₂ e₃ _ _ _ _
      (norms_of_induces (Setup.induces_root0 D O hO.dualRef _ c W _ subset_rfl x))).congr (fun _ => pow_one _)
      (fun _ _ => by simp) fun _ _ _ => by simp⟩
  refine ⟨V, M, hM, fun τ i hi => ?_⟩
  have hb : GlobalTheory.ShFam.Pad.ArIn.ind Q l = true := decide_eq_true hlQ
  have hp : O.S.Dw.p = O.j := O.S.p_eq
  have hpq : O.S.Dw.p + O.S.Dw.q = O.N := O.S.rank_eq
  have hτ (τ : D.what₂.Tau) : O.S.Dw.mult (DV.tauEmb D τ) = O.j := GlobalTheory.LocM.Check.mult_tau (S := O.S) τ
  have hcj (τ : D.what₂.Tau) : O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) + O.j = O.N := GlobalTheory.LocM.Check.mult_conj (S := O.S) τ
  have hj := O.indef.2

  have hR (x : DV.Rt D.what₂.Tau O.N) : ∃ (σ : D.host.E →+* ℂ) (k : ℕ) (hk : k < O.S.Dw.mult σ) (n : ℤ) (a' : _),
      Norms V (M x) (fun y => ((dg (O.Φ.C c) y σ ⟨k, hk⟩ ^ (-n) : (O.var c).Fnˣ) : (O.var c).Fn)) a'
        (fun v e y => n * symLog (O.Φ.C c) (GlobalTheory.ShFam.Pad.ArIn.ind Q) (.inl (σ, k)) v e y) ∧
      (x.2.val < O.j → σ = DV.tauEmb D x.1 ∧ k = x.2 ∧ n = 1) ∧
      (O.j ≤ x.2.val → σ = conjEmb (DV.tauEmb D x.1) ∧ k = O.N - 1 - x.2 ∧ n = -1) := by
    have hx := x.2.2
    by_cases hxj : x.2.val < O.j
    · obtain ⟨a', h'⟩ := norms_single (O.Φ.C c) (GlobalTheory.ShFam.Pad.ArIn.ind Q) (DV.tauEmb D x.1) (k := x.2) (by rw [hτ]; exact hxj) 1
        (if_pos (by omega)) (hM x)
      exact ⟨_, _, _, _, a', h', fun _ => ⟨rfl, rfl, rfl⟩, fun h => by omega⟩
    · have := hcj x.1
      obtain ⟨a', h'⟩ := norms_single (O.Φ.C c) (GlobalTheory.ShFam.Pad.ArIn.ind Q) (conjEmb (DV.tauEmb D x.1)) (k := O.N - 1 - x.2)
        (by omega) (-1) ((if_neg (by omega)).trans (by rw [hpq])) (hM x)
      exact ⟨_, _, _, _, a', h', fun h => absurd h hxj, fun _ => ⟨rfl, rfl, rfl⟩⟩
  choose σ k hk n a' hR h₁ h₂ using hR
  have step (s : D.host.E →+* ℂ) (m : ℕ) (hm : m ≤ O.S.Dw.mult s) (e : Fin m → DV.Rt D.what₂.Tau O.N)
      (he : Function.Injective e) (w : DV.Rt D.what₂.Tau O.N → ℤ) (u : ℤ) (hu : u * u = 1) (w₀ : ∀ x, x ∉ Set.range e → w x = 0)
      (w₁ : ∀ r, w (e r) = u) (hs : ∀ r, σ (e r) = s ∧ k (e r) = r ∧ n (e r) = -u) : NefOver (ArInt.comb M w) l := by
    refine nefOver_step (O.Φ.C c) hX V ρ'' e₄ hc hb s hm ((norms_comb hR w).congr (fun y => ?_) (fun _ _ => rfl)
      fun v ε y => ?_)
    · simp only [← Units.val_zpow_eq_zpow_val, ← Units.coe_prod]
      rw [prod_zpow_of_injective e he _ w u w₀ w₁]
      refine congrArg _ (Finset.prod_congr rfl fun r _ => ?_)
      obtain ⟨q₁, q₂, q₃⟩ := hs r
      have := hk (e r)
      rw [q₃, neg_neg, ← zpow_mul, hu, zpow_one]
      revert this
      generalize hk (e r) = q₄
      revert q₄
      rw [q₁, q₂]
      intro _ _
      rfl
    · rw [← Finset.sum_neg_distrib]
      refine (Fintype.sum_of_injective e he _ _ (fun x hx => by rw [w₀ x hx]; simp) fun r => ?_).symm
      obtain ⟨q₁, q₂, q₃⟩ := hs r
      have hu' : (u : ℝ) * u = 1 := by exact_mod_cast hu
      rw [w₁, q₁, q₂, q₃, Fin.val_castLE]
      push_cast
      linear_combination (symLog (O.Φ.C c) (GlobalTheory.ShFam.Pad.ArIn.ind Q) (.inl (s, r)) v ε y) * hu'
  by_cases hij : i ≤ O.j
  · have h₃ := step (DV.tauEmb D τ) i (by rw [hτ]; exact hij) (fun r => (τ, ⟨r, by omega⟩))
      (fun r r' e => Fin.ext (congrArg (fun x : DV.Rt D.what₂.Tau O.N => x.2.val) e))
      (fun x => if x.1 = τ ∧ x.2.val < i then -1 else 0) (-1) (by norm_num)
      (fun x hx => if_neg fun ⟨q₁, q₂⟩ => hx ⟨⟨x.2, q₂⟩, by rw [← q₁]⟩) (fun r => if_pos ⟨rfl, r.2⟩)
      fun r => h₁ _ (lt_of_lt_of_le r.2 hij)
    exact h₃
  · have hτ' := hcj τ
    have h₃ := step (conjEmb (DV.tauEmb D τ)) (O.N - i) (by omega) (fun r => (τ, ⟨O.N - 1 - r, by omega⟩))
      (fun r r' e => Fin.ext (by
        have : O.N - 1 - r = O.N - 1 - r' := congrArg (fun x : DV.Rt D.what₂.Tau O.N => x.2.val) e
        omega))
      (fun x => if x.1 = τ ∧ i ≤ x.2.val then 1 else 0) 1 (by norm_num)
      (fun x hx => if_neg fun ⟨q₁, q₂⟩ => hx ⟨⟨O.N - 1 - x.2, by omega⟩, Prod.ext q₁.symm (Fin.ext (by
        have := x.2.2
        show O.N - 1 - (O.N - 1 - x.2) = x.2
        omega))⟩)
      (fun r => if_pos ⟨rfl, by show i ≤ O.N - 1 - r; omega⟩)
      fun r => by
        obtain ⟨q₁, q₂, q₃⟩ := h₂ (τ, ⟨O.N - 1 - r, by omega⟩) (by show O.j ≤ O.N - 1 - r; omega)
        exact ⟨q₁, q₂.trans (by show O.N - 1 - (O.N - 1 - r) = r; omega), q₃⟩
    refine nefOver_of_icls V.ar one_pos ?_ (GlobalTheory.T.adelic_norm_nef_indicators h2 hH D O hO hf A T H h c Q l hlQ hl V M hM τ).2 h₃
    rw [one_nsmul, icls_comb, icls_comb, icls_comb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← add_smul]
    congr 1
    by_cases q₁ : x.1 = τ <;> by_cases q₂ : x.2.val < i <;> simp [q₁, q₂]
    omega

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseEqOfMatchingPullbacks
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

theorem GlobalTheory.UCanon.PairBase.spMap_comp {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : B →+* C') (g : A →+* B) :
    spMap (f.comp g) = spMap f ≫ spMap g := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

namespace GlobalTheory.UCanon.PairBase

theorem comp_pow {S : Scheme.{0}} {X Y M : Over S} [MonObj M] (f : X ⟶ Y) (g : Y ⟶ M) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem c_pow {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Sp R)) (y : D.X) (n : ℕ)
    (u v : T ⟶ D.P.A) (hu : u.left = T.hom ≫ (D.c y).left) (hv : v.left = T.hom ≫ (D.c (n • y)).left) : u ^ n = v := by
  have eu : u = toUnit T ≫ D.c y := Over.OverMorphism.ext (by rw [hu, Over.comp_left, Over.toUnit_left])
  have ev : v = toUnit T ≫ D.c (n • y) := Over.OverMorphism.ext (by rw [hv, Over.comp_left, Over.toUnit_left])
  rw [eu, ev, GlobalTheory.UCanon.LevLift.degPre_cocharPoint_nsmul_eq_pow_levelLift, comp_pow]

theorem etaA_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H}
    {c : Coeff l} (L : LowBase D' c) (T : Over (Sp L.W)) (a : D'.La) (u : T ⟶ L.D.P.A)
    (hu : u.left = T.hom ≫ (L.o.etaA a).left ≫ L.φB) : u ^ l.M' = 1 := by
  have h0 : L.o.etaA 0 = 1 := by
    have h := L.o.etaA_add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := L.o.etaA 0) (by rw [_root_.mul_one]; exact h.symm)
  have hn : ∀ n : ℕ, L.o.etaA (n • a) = L.o.etaA a ^ n := by
    intro n
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, L.o.etaA_add, ih, pow_succ]
  have hη : L.o.etaA a ^ l.M' = 1 := by
    rw [← hn]
    exact L.o.etaA_ker a
  let x : T ⟶ L.o.t.G := toUnit T ≫ L.o.etaA a
  have hx : x ^ l.M' = 1 := by
    rw [← comp_pow, hη, MonObj.comp_one]
  have hw : (x.left ≫ L.φB) ≫ L.D.P.A.hom = (Over.mk (T.hom ≫ 𝟙 _)).hom := by
    rw [Category.assoc, L.ab.1.1.w, ← Category.assoc, Over.w x]
    rfl
  let x₀ : Over.mk (T.hom ≫ 𝟙 _) ⟶ L.D.P.A := Over.homMk (x.left ≫ L.φB) hw
  have hp := GlobalTheory.FamTorsion.pow_left_of_isGrpPullback L.ab.1 x x₀ rfl l.M'
  have hx₀ : x₀ ^ l.M' = 1 := Over.OverMorphism.ext (by
    rw [hp, hx, GlobalTheory.FamTorsion.one_left_of_isGrpPullback L.ab.1 T])
  let e : T ⟶ Over.mk (T.hom ≫ 𝟙 _) := Over.homMk (𝟙 _) (by simp)
  have hue : u = e ≫ x₀ := Over.OverMorphism.ext (by
    rw [hu, Over.comp_left]
    simp [e, x₀, x, Over.toUnit_left])
  rw [hue, ← comp_pow, hx₀, MonObj.comp_one]

end GlobalTheory.UCanon.PairBase

theorem GlobalTheory.UCanon.PairBase.base_eq_of_match : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (∀ p₀ : QkPt C.P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) l.M') (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) l.M'), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → (letI := H.starRing; ∀ x : 𝓞 E, ∃ (a₁ : D₁.toPre.P.A ⟶ D₁.toPre.P.A) (a₂ : D₂.toPre.P.A ⟶ D₂.toPre.P.A), a₁ ≫ hD₁.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf f₁)).map (C.P.oD.onB.act x) ∧ a₂ ≫ hD₂.e.hom = hD₂.e.hom ≫ (Over.pullback (specOf f₂)).map (C.P.oD.onB.act x) ∧ a₁ ≫ b = b ≫ a₂) → (∀ y : C.P.D.toPre.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y) → f₁.comp C.b = f₂.comp C.b → f₁.comp (Cn.ψ.comp MvPolynomial.C) = f₂.comp (Cn.ψ.comp MvPolynomial.C) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hR C Cn V _ _ _ _ hV f₁ f₂ hi₁ hi₂ hl₁ hl₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b φ' hE₁ hE₂ hM hpts hact hφ hb
  obtain ⟨g, hD, hg, hxe, hoa⟩ := Cn.data
  have hβ : IsGrpPullback C.P.D.toPre.P.A Cn.L.D.P.A (spMap (Cn.ψ.comp MvPolynomial.C))
      (hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C))) := pull_grp hD
  set β : C.P.D.toPre.P.A.left ⟶ Cn.L.D.P.A.left := hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C)) with hβdef
  set π₁ : D₁.toPre.P.A.left ⟶ Cn.L.D.P.A.left := prj hD₁ ≫ β with hπ₁
  set π₂ : D₁.toPre.P.A.left ⟶ Cn.L.D.P.A.left := b.left ≫ prj hD₂ ≫ β with hπ₂
  have hp₁ : IsGrpPullback D₁.toPre.P.A Cn.L.D.P.A (spMap (f₁.comp (Cn.ψ.comp MvPolynomial.C))) π₁ :=
    ((pull_grp hD₁).comp hβ).congr (GlobalTheory.UCanon.PairBase.spMap_comp _ _).symm rfl
  haveI := hM.2.1
  haveI : IsMonHom (asIso b).hom := hM.1
  have hp₂ : IsGrpPullback D₁.toPre.P.A Cn.L.D.P.A (spMap (f₂.comp (Cn.ψ.comp MvPolynomial.C))) π₂ :=
    ((isGrpPullback_of_iso (asIso b)).comp ((pull_grp hD₂).comp hβ)).congr (by rw [Category.id_comp]; exact (GlobalTheory.UCanon.PairBase.spMap_comp f₂ _).symm) (by rw [hπ₂, asIso_hom])

  letI := H.starRing
  have hsq : ∀ {R' : Type} [CommRing R'] [IsDomain R'] {θ : R →+* R'} {D' : DegPre R'} (h : IsPullDeg θ C.P.D.toPre D')
      (f : C.P.D.toPre.P.A ⟶ C.P.D.toPre.P.A) (f' : D'.P.A ⟶ D'.P.A),
      f' ≫ h.e.hom = h.e.hom ≫ (Over.pullback (specOf θ)).map f → f'.left ≫ prj h = prj h ≫ f.left :=
    fun h f f' e => (GlobalTheory.PullDegTop.main.2.1 h f f').1 e
  have hoa' : letI := H.starRing; ∀ x, (C.P.oD.onB.act x).left ≫ β = β ≫ (Cn.L.oa.onB.act x).left :=
    fun x => (hoa x).trans (Category.assoc _ _ _).symm

  have hLB0 := GlobalTheory.T.lineBundleIso_of_action_compatible_match Xo c φ R hR C Cn V hV f₁ f₂ hi₁ hi₂ hl₁ hl₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b φ' hE₁ hE₂ hM hact
  have hβL : LBIso C.P.D.toPre.P.L (Cn.L.D.P.L.pull β) := ⟨hD.w, hD.w_gen⟩
  have hC := C.P.D.toPre.P.isLB
  have hLD := Cn.L.D.P.isLB
  have hW₁ : LBIso D₁.toPre.P.L (Cn.L.D.P.L.pull π₁) :=
    LBIso.trans D₁.toPre.P.isLB (pull_isLB hC _) (pull_isLB hLD _) ⟨hD₁.w, hD₁.w_gen⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp hβL (prj hD₁) rfl)
  have hW₂ : LBIso D₂.toPre.P.L (Cn.L.D.P.L.pull (prj hD₂ ≫ β)) :=
    LBIso.trans D₂.toPre.P.isLB (pull_isLB hC _) (pull_isLB hLD _) ⟨hD₂.w, hD₂.w_gen⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp hβL (prj hD₂) rfl)
  have hLB : LBIso (Cn.L.D.P.L.pull π₁) (Cn.L.D.P.L.pull π₂) :=
    LBIso.trans (pull_isLB hLD _) D₁.toPre.P.isLB (pull_isLB hLD _) hW₁.symm
      (LBIso.trans D₁.toPre.P.isLB (pull_isLB D₂.toPre.P.isLB _) (pull_isLB hLD _) hLB0
        (GlobalTheory.PolDeg.lbIso_pull_comp hW₂ b.left hπ₂))
  choose a₁ a₂ ha₁ ha₂ hab using hact
  have hA₁ : letI := H.starRing; ∀ x, (a₁ x).left ≫ π₁ = π₁ ≫ (Cn.L.oa.onB.act x).left := by
    intro x
    have e1 := hsq hD₁ _ _ (ha₁ x)
    calc (a₁ x).left ≫ π₁ = ((a₁ x).left ≫ prj hD₁) ≫ β := (Category.assoc _ _ _).symm
      _ = prj hD₁ ≫ ((C.P.oD.onB.act x).left ≫ β) := by rw [e1, Category.assoc]
      _ = π₁ ≫ (Cn.L.oa.onB.act x).left := by rw [hoa' x, ← Category.assoc]
  have hA₂ : letI := H.starRing; ∀ x, (a₁ x).left ≫ π₂ = π₂ ≫ (Cn.L.oa.onB.act x).left := by
    intro x
    have e1 := hsq hD₂ _ _ (ha₂ x)
    have e3 : (a₁ x).left ≫ b.left = b.left ≫ (a₂ x).left := by rw [← Over.comp_left, hab x, Over.comp_left]
    have e3r : ∀ {Z : Scheme.{0}} (k : D₂.toPre.P.A.left ⟶ Z), (a₁ x).left ≫ b.left ≫ k = b.left ≫ (a₂ x).left ≫ k :=
      fun k => by rw [← Category.assoc, e3, Category.assoc]
    have e1r : ∀ {Z : Scheme.{0}} (k : C.P.D.toPre.P.A.left ⟶ Z), (a₂ x).left ≫ prj hD₂ ≫ k = prj hD₂ ≫ (C.P.oD.onB.act x).left ≫ k :=
      fun k => by rw [← Category.assoc, e1, Category.assoc]
    rw [hπ₂, e3r, e1r, hoa' x]
    simp only [Category.assoc]
  have hA₀ : ∀ x, (a₁ x).left ≫ D₁.toPre.P.A.hom = D₁.toPre.P.A.hom := fun x => Over.w (a₁ x)

  have hM1 : 1 ≤ l.M' := (GlobalTheory.LowDat.lowLevel l).A_pos
  let F₀ := AlgebraicClosure (FractionRing R)
  let F := AlgebraicClosure (FractionRing V)
  let j : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have hj : Function.Injective j :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  have hTF : (TF (R := V) F).hom = spMap j := (GlobalTheory.UCanon.PairBase.spMap_comp _ _).symm
  have hExt : ∀ (fi : R →+* V) (ji : F₀ →+* F), TInj.Ext fi ji →
      spMap ji ≫ (TF (R := R) F₀).hom = spMap j ≫ spMap fi := by
    intro fi ji hE
    have e : ji.comp ((algebraMap (FractionRing R) F₀).comp (algebraMap R (FractionRing R))) = j.comp fi :=
      RingHom.ext fun r => hE r
    have e1 : (TF (R := R) F₀).hom = spMap ((algebraMap (FractionRing R) F₀).comp (algebraMap R (FractionRing R))) :=
      (GlobalTheory.UCanon.PairBase.spMap_comp _ _).symm
    rw [e1, ← GlobalTheory.UCanon.PairBase.spMap_comp, e, GlobalTheory.UCanon.PairBase.spMap_comp]
  have hz : ∀ (y' : C.P.D.toPre.X) (x : TF (R := R) F₀ ⟶ C.P.D.toPre.P.A) (u : Sp R ⟶ Cn.L.D.P.A.left),
      x ^ l.M' = DegPre.cF C.P.D.toPre F₀ y' → x.left ≫ β = (TF (R := R) F₀).hom ≫ u →
      ∃ z : Sp F ⟶ D₁.toPre.P.A.left, z ≫ D₁.toPre.P.A.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ u ∧
        z ≫ π₂ = spMap j ≫ spMap f₂ ≫ u := by
    intro y' x u hx hxu
    obtain ⟨z, hz₁, hz₂⟩ := GlobalTheory.T.divisionPoints_correspond_matched_pullbacks R V C.P.D.toPre D₁.toPre D₂.toPre C.P.D.tau_bimult D₂.tau_bimult f₁ f₂ hD₁ hD₂
      F₀ F j₁ j₂ b φ' l.M' hM1 hpts hφ y' x hx
    have hz₁' : z.left ≫ prj hD₁ = spMap j₁ ≫ x.left := hz₁
    have hz₂' : z.left ≫ b.left ≫ prj hD₂ = spMap j₂ ≫ x.left := hz₂
    refine ⟨z.left, by rw [Over.w z, hTF], ?_, ?_⟩
    · calc z.left ≫ π₁ = (z.left ≫ prj hD₁) ≫ β := by rw [hπ₁]; simp only [Category.assoc]
        _ = (spMap j₁ ≫ (TF (R := R) F₀).hom) ≫ u := by rw [hz₁', Category.assoc, hxu, Category.assoc]
        _ = spMap j ≫ spMap f₁ ≫ u := by rw [hExt f₁ j₁ hE₁, Category.assoc]
    · calc z.left ≫ π₂ = (z.left ≫ b.left ≫ prj hD₂) ≫ β := by rw [hπ₂]; simp only [Category.assoc]
        _ = (spMap j₂ ≫ (TF (R := R) F₀).hom) ≫ u := by rw [hz₂', Category.assoc, hxu, Category.assoc]
        _ = spMap j ≫ spMap f₂ ≫ u := by rw [hExt f₂ j₂ hE₂, Category.assoc]

  have hlift : ∀ (y' : C.P.D.toPre.X) (u : Sp R ⟶ Cn.L.D.P.A.left),
      u ≫ Cn.L.D.P.A.hom = spMap (Cn.ψ.comp MvPolynomial.C) →
      (∀ w w' : Over.mk ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C)) ⟶ Cn.L.D.P.A,
        w.left = (TF (R := R) F₀).hom ≫ u →
        w'.left = (TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c (l.M' • Cn.e y')).left →
        w ^ l.M' = w') →
      ∃ x : TF (R := R) F₀ ⟶ C.P.D.toPre.P.A, x ^ l.M' = DegPre.cF C.P.D.toPre F₀ y' ∧
        x.left ≫ β = (TF (R := R) F₀).hom ≫ u := by
    intro y' u hu H'
    have hw0 : ((TF (R := R) F₀).hom ≫ u) ≫ Cn.L.D.P.A.hom =
        (TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) := by rw [Category.assoc, hu]
    let x : TF (R := R) F₀ ⟶ C.P.D.toPre.P.A := Over.homMk (hβ.1.lift _ _ hw0) (hβ.1.lift_snd _ _ _)
    have hxβ : x.left ≫ β = (TF (R := R) F₀).hom ≫ u := hβ.1.lift_fst _ _ _
    refine ⟨x, ?_, hxβ⟩
    let w : Over.mk ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C)) ⟶ Cn.L.D.P.A :=
      Over.homMk ((TF (R := R) F₀).hom ≫ u) hw0
    have hc0 : ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c (l.M' • Cn.e y')).left) ≫
        Cn.L.D.P.A.hom = (TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) := by
      simp only [Category.assoc]
      erw [Over.w (Cn.L.D.c (l.M' • Cn.e y'))]
      simp
    let w' : Over.mk ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C)) ⟶ Cn.L.D.P.A := Over.homMk _ hc0
    have hw := H' w w' rfl rfl
    have hpow := GlobalTheory.FamTorsion.pow_left_of_isGrpPullback hβ x w hxβ.symm l.M'
    apply Over.OverMorphism.ext
    apply hβ.1.hom_ext
    · rw [← hpow, hw]
      have hcp := hD.c_pr y'
      show (TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c (l.M' • Cn.e y')).left =
        (toUnit (TF (R := R) F₀) ≫ C.P.D.toPre.c y').left ≫ β
      rw [Over.comp_left, Over.toUnit_left, Category.assoc]
      erw [hcp]
      rw [hxe]
      rfl
    · rw [Over.w, Over.w]
  have hEta : ∀ a, ∃ z : Sp F ⟶ D₁.toPre.P.A.left, z ≫ D₁.toPre.P.A.hom = spMap j ∧
      z ≫ π₁ = spMap j ≫ spMap (f₁.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.o.etaA a).left ≫ Cn.L.φB ∧
      z ≫ π₂ = spMap j ≫ spMap (f₂.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.o.etaA a).left ≫ Cn.L.φB := by
    intro a
    have hu : (spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.o.etaA a).left ≫ Cn.L.φB) ≫ Cn.L.D.P.A.hom =
        spMap (Cn.ψ.comp MvPolynomial.C) := by
      rw [Category.assoc, Category.assoc, Cn.L.ab.1.1.w, Category.comp_id, Over.w (Cn.L.o.etaA a)]
      simp
    obtain ⟨x, hx, hxu⟩ := hlift 0 _ hu (fun w w' hw hw' => by
      have e1 : w ^ l.M' = 1 := GlobalTheory.UCanon.PairBase.etaA_pow Cn.L _ a w (by rw [hw]; simp only [Over.mk_hom, Category.assoc])
      have h0 : w'.left = (Over.mk ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C))).hom ≫ (Cn.L.D.c 0).left := by
        rw [hw', map_zero, smul_zero]; simp only [Over.mk_hom, Category.assoc]
      have e2 := GlobalTheory.UCanon.PairBase.c_pow Cn.L.D _ 0 0 w' w' h0 (by rw [h0, zero_smul])
      rw [pow_zero] at e2
      rw [e1, e2])
    obtain ⟨z, hz0, hz1, hz2⟩ := hz 0 x _ hx hxu
    refine ⟨z, hz0, ?_, ?_⟩
    · rw [hz1, GlobalTheory.UCanon.PairBase.spMap_comp f₁ (Cn.ψ.comp MvPolynomial.C)]; simp only [Category.assoc]
    · rw [hz2, GlobalTheory.UCanon.PairBase.spMap_comp f₂ (Cn.ψ.comp MvPolynomial.C)]; simp only [Category.assoc]
  have hCp : ∀ y, ∃ z : Sp F ⟶ D₁.toPre.P.A.left, z ≫ D₁.toPre.P.A.hom = spMap j ∧
      z ≫ π₁ = spMap j ≫ spMap (f₁.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left ∧
      z ≫ π₂ = spMap j ≫ spMap (f₂.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left := by
    intro y
    have hu : (spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c y).left) ≫ Cn.L.D.P.A.hom =
        spMap (Cn.ψ.comp MvPolynomial.C) := by
      rw [Category.assoc, Over.w (Cn.L.D.c y)]
      simp
    obtain ⟨x, hx, hxu⟩ := hlift (Cn.e.symm y) _ hu (fun w w' hw hw' =>
      GlobalTheory.UCanon.PairBase.c_pow Cn.L.D _ y l.M' w w' (by rw [hw]; simp only [Over.mk_hom, Category.assoc])
        (by rw [hw', Cn.e.apply_symm_apply]; simp only [Over.mk_hom, Category.assoc]))
    obtain ⟨z, hz0, hz1, hz2⟩ := hz _ x _ hx hxu
    refine ⟨z, hz0, ?_, ?_⟩
    · rw [hz1, GlobalTheory.UCanon.PairBase.spMap_comp f₁ (Cn.ψ.comp MvPolynomial.C)]; simp only [Category.assoc]
    · rw [hz2, GlobalTheory.UCanon.PairBase.spMap_comp f₂ (Cn.ψ.comp MvPolynomial.C)]; simp only [Category.assoc]
  have hbase : (f₁.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b = (f₂.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b := by
    have e : ∀ f : R →+* V, (f.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b = f.comp C.b := fun f => by
      rw [← Cn.base]; rfl
    rw [e, e, hb]
  exact (GlobalTheory.UCanon.FineAgree.main Cn.L V _ _ hbase D₁.toPre.P.A π₁ π₂ (fun x => (a₁ x).left) hp₁ hp₂ hA₁ hA₂ hA₀ hLB F j hj
    hEta hCp).1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreCechCocycleInTangentSpanStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_cechCocycle_in_tangentSpan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ θ : Fin n → Γ(X, U.1), ∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i' - ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i') := by
  first | exact @GlobalTheory.FibreSpan.fibre_span | exact GlobalTheory.FibreSpan.fibre_span | (intros; apply GlobalTheory.FibreSpan.fibre_span <;> assumption)
end

