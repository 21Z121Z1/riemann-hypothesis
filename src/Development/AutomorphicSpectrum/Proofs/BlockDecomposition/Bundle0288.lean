import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0267
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0278
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0277
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0279
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0276
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0280
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowDvdFactorialMul
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickLine

theorem pow_dvd_factorial_mul {p : ℕ} (hp : p.Prime) (N : ℕ) : p ^ N ∣ (p * N).factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, pow_succ]
    exact (mul_dvd_mul ih (Nat.dvd_factorial hp.pos le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem isNilpotent_of_mem {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) {p : ℕ} (hp : p.Prime)
    (hn : IsNilpotent (p : A)) {x : A} (hx : x ∈ J) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hn
  obtain ⟨k, hk⟩ := pow_dvd_factorial_mul hp N
  refine ⟨p * N, ?_⟩
  rw [← δ.factorial_mul_dpow_eq_pow hx, hk]
  push_cast
  rw [hN]
  simp

theorem ringHom_eq {B C : Type} [CommRing B] [CommRing C] (Q : PDPoly B) {f g : Q.P →+* C}
    (h1 : ∀ b, f (algebraMap B Q.P b) = g (algebraMap B Q.P b)) (h2 : ∀ k, f (Q.e k) = g (Q.e k)) : f = g := by
  ext p
  have hp : p ∈ Submodule.span B (Set.range Q.e) := Q.e.mem_span p
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h2 k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul b x _ hx => rw [Algebra.smul_def, map_mul, map_mul, hx, h1]

theorem e_one_mem {B : Type} [CommRing B] (Q : PDPoly B) (J : Ideal B) : Q.e 1 ∈ Q.ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem le_comap_ext {B : Type} [CommRing B] (Q : PDPoly B) (J : Ideal B) :
    J ≤ (Q.ext J).comap (algebraMap B Q.P) :=
  fun _ hx => Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)

variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem s_eq_one (T : Thick (F.cr b ht κ)) : T.s = 1 := by
  have h : (1 : T.B) = T.s * T.i b.t := (Finset.prod_of_isEmpty (ι := Empty) _).symm.trans T.hs
  rw [ht, map_one, mul_one] at h
  exact Units.ext h.symm

variable (T : Thick (F.cr b ht κ)) (Q : PDPoly T.B) (η₀ : DividedPowers (Q.ext T.J)) (hη : Q.IsStd T.δ η₀)
  (hp : b.p ≠ 0)

def line : Thick (F.cr b ht κ) where
  B := Q.P
  i := (algebraMap T.B Q.P).comp T.i
  J := Q.ext T.J
  δ := η₀
  adm := ⟨fun _ => by simpa using (T.adm.1 hp).map (algebraMap T.B Q.P), fun h => absurd h hp⟩
  compat := IsDPMorphism.comp _ hη.dp T.compat
  α := ()
  y := (F.cr b ht κ).Pt.map
    (CommRingCat.ofHom (Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J))) T.y
  inα := trivial
  w r := by
    change Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J)
      ((F.cr b ht κ).str T.y (Ideal.Quotient.mk _ r)) = _
    rw [T.w r]
    rfl
  x j := j.elim
  v j := j.elim
  s := 1
  hx j := j.elim
  hs := (Finset.prod_of_isEmpty (ι := Empty) _).trans (by rw [ht]; simp)
  hv := (map_one _).trans (Finset.prod_of_isEmpty (ι := Empty) _).symm

def toLine : T ⟶ line T Q η₀ hη hp where
  φ := algebraMap T.B Q.P
  u j := j.elim
  comm _ := rfl
  dp := hη.dp
  hle := le_comap_ext Q T.J
  pt := rfl
  hx j := j.elim
  hs := by
    rw [s_eq_one T, map_one, mul_one]
    exact (Finset.prod_of_isEmpty (ι := Empty) _).symm
  hv j := j.elim

variable {T Q η₀ hη hp}

theorem exists_ext {T' : Thick (F.cr b ht κ)} (φ : T ⟶ T') {c : T'.B} (hc : c ∈ T'.J) :
    ∃ ψ : line T Q η₀ hη hp ⟶ T', toLine T Q η₀ hη hp ≫ ψ = φ ∧ ψ.φ (Q.e 1) = c := by
  obtain ⟨G, hG1, hG2⟩ := FubiniStudyChowHeightFormula₂.Adr.Fil.exists_lift Q T'.B φ.φ (fun k => T'.δ.dpow k c) (T'.δ.dpow_zero hc) (fun m k => T'.δ.mul_dpow hc)
  have hGa : G.comp (algebraMap T.B Q.P) = φ.φ := RingHom.ext hG1
  have hGdp : IsDPMorphism η₀ T'.δ G :=
    FubiniStudyChowHeightFormula₂.Adr.dp_of_std T.δ Q η₀ hη T'.δ G c hc (by rw [hGa]; exact φ.dp) hG2
  have hle : Q.ext T.J ≤ T'.J.comap G := Ideal.map_le_iff_le_comap.1 hGdp.1
  refine ⟨{ φ := G, u := fun j => j.elim, comm := fun r => ?_, dp := hGdp, hle := hle, pt := ?_,
            hx := fun j => j.elim, hs := ?_, hv := fun j => j.elim }, ?_, ?_⟩
  · exact (hG1 _).trans (φ.comm r)
  · refine Eq.trans ?_ φ.pt
    have e : CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle) =
        CommRingCat.ofHom (Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J)) ≫
          CommRingCat.ofHom (Ideal.quotientMap T'.J G hle) := by
      refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      change Ideal.Quotient.mk T'.J (φ.φ a) = Ideal.Quotient.mk T'.J (G (algebraMap T.B Q.P a))
      rw [hG1]
    rw [e, Functor.map_comp]
    rfl
  · rw [s_eq_one T']
    refine Units.ext ?_
    change (1 : T'.B) = ((∏ j : Empty, (j.elim : T'.Bˣ)) * Units.map G.toMonoidHom 1 : T'.Bˣ)
    simp
  · exact Thick.Hom.ext hGa (funext fun j => j.elim)
  · change G (Q.e 1) = c
    rw [hG2 1]
    exact T'.δ.dpow_one hc

theorem hom_unique {T' : Thick (F.cr b ht κ)} {ψ ψ' : line T Q η₀ hη hp ⟶ T'}
    (h : toLine T Q η₀ hη hp ≫ ψ = toLine T Q η₀ hη hp ≫ ψ') (he : ψ.φ (Q.e 1) = ψ'.φ (Q.e 1)) : ψ = ψ' := by
  refine Thick.Hom.ext (ringHom_eq Q (fun a => ?_) fun k => ?_) (funext fun j => j.elim)
  · exact congrArg (fun f : T ⟶ T' => f.φ a) h
  · have h1 : T'.δ.dpow k (ψ.φ (Q.e 1)) = ψ.φ (η₀.dpow k (Q.e 1)) := ψ.dp.2 (Q.e 1) (e_one_mem Q T.J)
    have h2 : T'.δ.dpow k (ψ'.φ (Q.e 1)) = ψ'.φ (η₀.dpow k (Q.e 1)) := ψ'.dp.2 (Q.e 1) (e_one_mem Q T.J)
    rw [hη.var k] at h1 h2
    have h3 : T'.δ.dpow k (ψ.φ (Q.e 1)) = T'.δ.dpow k (ψ'.φ (Q.e 1)) := congrArg _ he
    exact h1.symm.trans (h3.trans h2)

def lineU (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (hpp : b.p.Prime) :
    (thU (F.cr b ht κ) q hq).U (line T Q η₀ hη hpp.ne_zero) :=
  ⟨(isNilpotent_of_mem η₀ hpp (by simpa using (T.adm.1 hpp.ne_zero).map (algebraMap T.B Q.P))
      (e_one_mem Q T.J)).isUnit_one_add.unit,
    MonoidHom.mem_ker.2 (Units.ext (by
      change Ideal.Quotient.mk (Q.ext T.J) (1 + Q.e 1) = Ideal.Quotient.mk (Q.ext T.J) 1
      exact Ideal.Quotient.eq.2 (by simpa using e_one_mem Q T.J)))⟩

theorem map_lineU {T' : Thick (F.cr b ht κ)} (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (hpp : b.p.Prime)
    (ψ : line T Q η₀ hη hpp.ne_zero ⟶ T') :
    ((((thU (F.cr b ht κ) q hq).map ψ (lineU q hq hpp)).1 : T'.Bˣ) : T'.B) = 1 + ψ.φ (Q.e 1) := by
  change (ψ.φ : Q.P →+* T'.B) ((1 : Q.P) + Q.e 1) = 1 + _
  exact (map_add (ψ.φ : Q.P →+* T'.B) 1 (Q.e 1)).trans (by rw [map_one]; rfl)

theorem main : ∀ {O : Type} [CommRing O] (F : Fn O) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (ρ : ℕ → ℕ) (hρ : Slow ρ) (μ : Λ) (hμ : c μ ∈ b.I) (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (x : b.R), b.p.Prime → (q : b.R) = x ^ b.p → c μ = q - 1 → (∑ i ∈ Finset.range b.p, x ^ i) ∈ b.I → ∀ T : Thick (F.cr b ht κ), ∃ (T₁ : Thick (F.cr b ht κ)) (i : T ⟶ T₁) (η : (thU (F.cr b ht κ) q hq).U T₁), (∀ (T' : Thick (F.cr b ht κ)) (φ : T ⟶ T') (a : (thU (F.cr b ht κ) q hq).U T'), ∃! ψ : T₁ ⟶ T', i ≫ ψ = φ ∧ (thU (F.cr b ht κ) q hq).map ψ η = a) ∧ ∀ g : T₁ ⟶ T₁, i ≫ g = i → (thU (F.cr b ht κ) q hq).map g η = (thU (F.cr b ht κ) q hq).q _ * η → (pdFlt (F.cr b ht κ) c ρ hρ μ hμ).FAcyc i g := by
  intro O _ F b ht κ Λ _ c ρ hρ μ hμ q hq x hpp hqx hcμ hsum T
  have hp0 := hpp.ne_zero
  obtain ⟨Q⟩ : Nonempty (PDPoly T.B) := ⟨GlobalTheory.PDA.Model.pdPoly T.B⟩
  obtain ⟨η₀, hη⟩ := FubiniStudyChowHeightFormula₂.Adr.exists_std T.B T.J T.δ Q
  refine ⟨line T Q η₀ hη hp0, toLine T Q η₀ hη hp0, lineU q hq hpp, ?_, ?_⟩
  · intro T' φ a
    have hc : ((a.1 : T'.Bˣ) : T'.B) - 1 ∈ T'.J := by
      have h : Ideal.Quotient.mk T'.J ((a.1 : T'.Bˣ) : T'.B) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 a.2)
      exact Ideal.Quotient.eq.1 (h.trans (map_one _).symm) |> fun h => by simpa using h
    obtain ⟨ψ, h1, h2⟩ := exists_ext (Q := Q) (η₀ := η₀) (hη := hη) (hp := hp0) φ hc
    refine ⟨ψ, ⟨h1, ?_⟩, ?_⟩
    · refine Subtype.ext (Units.ext ?_)
      refine (map_lineU q hq hpp ψ).trans ?_
      rw [h2]
      ring
    · rintro ψ' ⟨h1', h2'⟩
      have e : 1 + ψ'.φ (Q.e 1) = ((a.1 : T'.Bˣ) : T'.B) := (map_lineU q hq hpp ψ').symm.trans
        (congrArg (fun u : (thU (F.cr b ht κ) q hq).U T' => ((u.1 : T'.Bˣ) : T'.B)) h2')
      refine hom_unique (h1'.trans h1.symm) ?_
      rw [h2]
      exact eq_sub_of_add_eq' e
  · intro g hg hgη
    let gφ : Q.P →+* Q.P := g.φ
    have hgφ : gφ.comp (algebraMap T.B Q.P) = algebraMap T.B Q.P :=
      congrArg (fun f : T ⟶ line T Q η₀ hη hp0 => f.φ) hg
    have hmul : gφ (1 + Q.e 1) = algebraMap T.B Q.P ((T.i x) ^ b.p) * (1 + Q.e 1) := by
      have e : gφ (1 + Q.e 1) = algebraMap T.B Q.P (T.i (q : b.R)) * (1 + Q.e 1) :=
        congrArg (fun u : (thU (F.cr b ht κ) q hq).U (line T Q η₀ hη hp0) =>
          ((u.1 : (line T Q η₀ hη hp0).Bˣ) : (line T Q η₀ hη hp0).B)) hgη
      rw [e, hqx, map_pow]
    have hsum' : (∑ i ∈ Finset.range b.p, (T.i x) ^ i) ∈ T.J := by
      have := T.i_mem hsum
      simpa [map_sum, map_pow] using this
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.CompanionTheory.PDAcyc.main T.δ Q η₀ hη b.p hpp (T.adm.1 hp0) (T.i x) hsum' gφ hgφ g.dp hmul
    have hμ' : ∀ z : Q.P, algebraMap T.B Q.P ((T.i x) ^ b.p - 1) * z =
        algebraMap T.B Q.P (T.i (c μ)) * z := by
      intro z
      rw [hcμ, hqx, map_sub T.i, map_pow, map_one]
    refine ⟨h1, ?_, ?_⟩
    · intro r z hz hz'
      obtain ⟨m, hm, e⟩ := h2 (ρ r) z hz hz'
      exact ⟨m, T.pdPow_anti (hρ.2 r) hm, e.trans (hμ' z)⟩
    · intro r z hz
      obtain ⟨y, hy, e⟩ := h3 (ρ r) z hz
      exact ⟨y, (line T Q η₀ hη hp0).pdPow_anti (hρ.2 r) hy, e.trans (hμ' z)⟩

end GlobalTheory.CompanionTheory.ThickLine
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardSystemAffineSections
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Chart

attribute [local instance] algebraOfOver

variable {X Z : Scheme.{0}}

theorem idealPowι_comp_pullback_map_cokernel_eq_zero {A : Type} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X)
    (hφ : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (E : X.Modules) (D : Subobject E) (m : ℕ)
    (hD : powSub I E m ≤ D) :
    idealPowι I ((Scheme.Modules.pullback φ).obj E) m ≫
      (Scheme.Modules.pullback φ).map (cokernel.π D.arrow) = 0 := by
  apply (cancel_epi (Abelian.factorThruImage
    (idealSumMap ((Scheme.Modules.pullback φ).obj E) (I ^ m)))).1
  rw [comp_zero, ← Category.assoc, Abelian.image.fac]
  apply biproduct.hom_ext'
  intro k
  rw [comp_zero, idealSumMap, biproduct.ι_desc_assoc, smulHom_comp, ← appTop_algebraMap φ hφ,
    ← pullback_map_smulHom_appTop, ← Functor.map_comp, ← smulHom_comp]
  obtain ⟨L, hL⟩ := exists_smulHom_eq_comp_idealSumMap E (I ^ m) (idealGen_mem (I ^ m) k)
  have hι : idealPowι I E m ≫ cokernel.π D.arrow = 0 := by
    have h := Subobject.ofMkLE_arrow (f := idealPowι I E m) (X := D) hD
    rw [← h, Category.assoc, cokernel.condition, comp_zero]
  rw [hL, ← Abelian.image.fac (idealSumMap E (I ^ m)), Category.assoc, Category.assoc, hι,
    comp_zero, comp_zero, Functor.map_zero]

theorem chartIn_of_pullback_app_eq_zero (φ : Z ⟶ X) {E : X.Modules} [E.IsQuasicoherent]
    (D : Subobject E) [(D : X.Modules).IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V)
    (x : Γ(E, V))
    (hx : ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ φ ⁻¹ᵁ V,
      ((Scheme.Modules.pullback φ).map (cokernel.π D.arrow)).app U
        (GlobalTheory.QCoh.pullbackSections φ E h x) = 0) :
    ChartIn φ V (secsSub D V) x := by
  intro U hU h
  letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
  have hx' := hx U hU h
  rw [GlobalTheory.QCoh.pullback_map_app_pullbackSections] at hx'
  letI := GlobalTheory.QCoh.appLEModule φ ((Scheme.Modules.pullback φ).obj (cokernel D.arrow)) h
  haveI := GlobalTheory.QCoh.appLE_isScalarTower φ ((Scheme.Modules.pullback φ).obj (cokernel D.arrow)) h
  have hbc := GlobalTheory.QCoh.isBaseChange_pullbackSections φ (cokernel D.arrow) hU hV h
  let πl : Γ(E, V) →ₗ[Γ(X, V)] Γ(cokernel D.arrow, V) :=
    { toFun := (cokernel.π D.arrow).app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  have hsurj : Function.Surjective πl := surjective_cokernel_π_app D.arrow hV
  have hex : Function.Exact (secsSub D V).subtype πl := by
    intro m
    have hm : m ∈ Set.range (secsSub D V).subtype ↔ m ∈ Set.range (D.arrow.app V) := by
      rw [Submodule.coe_subtype, Subtype.range_coe_subtype]
      rfl
    rw [hm, mem_range_app_iff D.arrow hV m]
    rfl
  have hex' := rTensor_exact Γ(Z, U) hex hsurj
  refine (hex' _).1 ?_
  rw [LinearMap.rTensor_tmul]
  have h1 : (1 : Γ(Z, U)) ⊗ₜ[Γ(X, V)] πl x = 0 := by
    apply hbc.equiv.injective
    rw [hbc.equiv_tmul, one_smul, map_zero]
    exact hx'
  rw [← TensorProduct.comm_tmul, h1, map_zero]

theorem chartIn_adjKer : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X),
    φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E →
    ∀ {S : ℕ → Subobject E}, ClosedSys I E S →
    ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)),
    (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∀ (V : X.Opens), IsAffineOpen V →
    ∀ x ∈ secs (adjKer φ B) V, ∀ n, ChartIn φ V (secsSub (S n) V) x := by
  intro A _ _ I X Z _ _ _ φ hφ E hE S hS B hB V hV x hx n
  have : E.IsQuasicoherent := hE.1
  have : ((S n : Subobject E) : X.Modules).IsQuasicoherent := hS.qcoh n
  apply chartIn_of_pullback_app_eq_zero φ (S n) V hV x
  intro U hU h
  obtain ⟨y, rfl⟩ := hx
  set g := (Scheme.Modules.pullback φ).map (cokernel.π (S n).arrow) with hg
  have hK : pullSys I φ E S n ≤ kernelSubobject g := by
    refine sup_le (image_le_kernel _ _ ?_) (le_kernelSubobject _ _ ?_)
    · rw [hg, ← Functor.map_comp, cokernel.condition, Functor.map_zero]
    · rw [powSub, ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
        idealPowι_comp_pullback_map_cokernel_eq_zero I φ hφ E (S n) (n + 1) (hS.pow_le n),
        comp_zero]
  have hBle : B ≤ kernelSubobject g := by
    rw [← hB n] at hK
    exact le_sup_left.trans hK
  have hBg : B.arrow ≫ g = 0 := by
    rw [← Subobject.ofLE_arrow hBle, Category.assoc, kernelSubobject_arrow_comp, comp_zero]
  have h0 : (adjMap φ B).app V ((adjKer φ B).arrow.app V y) = 0 := by
    have hk : (adjKer φ B).arrow ≫ adjMap φ B = 0 := kernelSubobject_arrow_comp _
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, hk]
    rfl
  have h1 : (cokernel.π B.arrow).app (φ ⁻¹ᵁ V)
      (((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app E).app V
        ((adjKer φ B).arrow.app V y)) = 0 := by
    rw [adjMap, Adjunction.homEquiv_unit] at h0
    exact h0
  have hfac : g = cokernel.π B.arrow ≫ cokernel.desc B.arrow g hBg := (cokernel.π_desc _ _ _).symm
  have h2 : (cokernel.π B.arrow).app U
      (GlobalTheory.QCoh.pullbackSections φ E h ((adjKer φ B).arrow.app V y)) = 0 := by
    rw [GlobalTheory.QCoh.pullbackSections_apply]
    erw [GlobalTheory.QCoh.hom_app_res (cokernel.π B.arrow) h]
    rw [h1, map_zero]
  rw [hfac, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, h2, map_zero]

end GlobalTheory.CompanionTheory.GE.Chart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionIntegralTraceAlmostAllStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_integral_trace_almost_all : ∀ {F : Type} [Field F] [NumberField F] (d β : F), d ≠ 0 → β ≠ 0 →
  ∀ᶠ v in Filter.cofinite (α := HeightOneSpectrum (𝓞 F)), ∀ t ∈ Ov v,
    ∃ b : Q d β (Kp (Sum.inr v : Pl F)), qn b = 1 ∧ 2 * b.re = t ∧ IntQ v b := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.exists_integral_norm_one_trace | exact GlobalTheory.CompanionTheory.PlaneSA.exists_integral_norm_one_trace | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.exists_integral_norm_one_trace <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionNormOneConjugateStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_norm_one_conjugate : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F), (2 : K) ≠ 0 → d ≠ 0 → β ≠ 0 →
  ∀ x b : Q d β K, qn x = 1 → qn b = 1 → x.re = b.re → x.re ^ 2 ≠ 1 →
    ∃ y : (Q d β K)ˣ, (y : Q d β K) * x * ((y⁻¹ : (Q d β K)ˣ) : Q d β K) = b := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.ConjQ.conj_of_same_re | exact GlobalTheory.CompanionTheory.PlaneSA.ConjQ.conj_of_same_re | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.ConjQ.conj_of_same_re <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRamifiedPlacesFiniteStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_ramified_places_finite : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ r : F, r ^ 2 ≠ d) → β ≠ 0 →
  {u : Pl F | ∀ x : Q d β (Kp u), qn x = 0 → x = 0}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.finite_anisotropic_places | exact GlobalTheory.CompanionTheory.PlaneSA.finite_anisotropic_places | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.finite_anisotropic_places <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRegularDenseStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_regular_dense : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalDivisionRing K] (d β : F),
  (2 : K) ≠ 0 → d ≠ 0 → β ≠ 0 → (𝓝[≠] (0 : K)).NeBot →
  ∀ a : Q d β K, qn a = 1 → ∀ U ∈ 𝓝 a, ∃ b ∈ U, qn b = 1 ∧ b.re ^ 2 ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.RegDense.regular_dense | exact GlobalTheory.CompanionTheory.PlaneSA.RegDense.regular_dense | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.RegDense.regular_dense <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionTraceOpenStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_trace_open : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalDivisionRing K] (d β : F)
  (a : Q d β K), qn a = 1 → a.re ^ 2 ≠ 1 →
  (∀ V ∈ 𝓝 (1 : K), ∀ᶠ x in 𝓝 (1 : K), ∃ μ ∈ V, μ ^ 2 = x) →
  ∀ U ∈ 𝓝 a, ∀ᶠ r in 𝓝 a.re, ∃ b ∈ U, qn b = 1 ∧ b.re = r := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.re_normOne_open_of_sq_ne_one | exact GlobalTheory.CompanionTheory.PlaneSA.re_normOne_open_of_sq_ne_one | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.re_normOne_open_of_sq_ne_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReflectionsGenerateSubgroupStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reflections_generate_subgroup : ∀ {R : Type} [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → ∀ {M : ℕ} (Jm : Matrix (Fin M) (Fin M) R), (∀ i j, c (Jm j i) = Jm i j) → ∀ a₀ : Fin M → R, IsUnit (Formalism.UG.hform c Jm a₀ a₀) → ∀ H : Subgroup (GL (Fin M) R), (∀ y ∈ Formalism.UG.UJ c Jm, IsQPair c Jm (y : Matrix (Fin M) (Fin M) R) → y ∈ H) → ∀ l : List (GL (Fin M) R), (∀ y ∈ l, y ∈ Formalism.UG.UJ c Jm ∧ IsQR c Jm (y : Matrix (Fin M) (Fin M) R)) → ((l.prod : GL (Fin M) R) : Matrix (Fin M) (Fin M) R).det = 1 → l.prod ∈ H := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.PairList.pair_of_list | exact GlobalTheory.CompanionTheory.SaGen.PairList.pair_of_list | (intros; apply GlobalTheory.CompanionTheory.SaGen.PairList.pair_of_list <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedSystemKilledByIdeal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem killed_restrictSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {E : X.Modules} (J : X.IdealSheafData)
    (D : Subobject E) (S : ℕ → Subobject E) (c : ℕ)
    (h : ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J.ideal U →
      ∀ x ∈ secs D U, a • x ∈ secs (S n) U) (e : ℕ) :
    Killed J (restrictSys I D S c e) := by
  intro U a ha x
  have hle : (Subobject.pullback D.arrow).obj (S (e + c)) ≤ GlobalTheory.CompanionTheory.GE.restrictSys I D S c e := by
    unfold GlobalTheory.CompanionTheory.GE.restrictSys
    exact le_sup_left
  have hmem : a • x ∈ GlobalTheory.CompanionTheory.GE.secs ((Subobject.pullback D.arrow).obj (S (e + c))) U := by
    rw [GlobalTheory.T.subobject_pullback_sections, Set.mem_preimage, Scheme.Modules.Hom.app_smul]
    exact h (e + c) U a ha _ (by unfold GlobalTheory.CompanionTheory.GE.secs; exact Set.mem_range_self x)
  unfold GlobalTheory.CompanionTheory.GE.secs at hmem ⊢
  obtain ⟨y, hy⟩ := hmem
  refine ⟨ConcreteCategory.hom (Scheme.Modules.Hom.app (Subobject.ofLE _ _ hle) U) y, ?_⟩
  rw [← hy, ← Subobject.ofLE_arrow hle, Scheme.Modules.Hom.comp_app] <;> rfl

end GlobalTheory.CompanionTheory.GE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecialSupportOfLocalLiftStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_support_of_local_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → ∀ g ∈ SUSupp σ J (P.inj 1), ∃ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 ∧ L x = g := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.exists_lift_of_mem_supp | exact GlobalTheory.CompanionTheory.SaGen.exists_lift_of_mem_supp | (intros; apply GlobalTheory.CompanionTheory.SaGen.exists_lift_of_mem_supp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecialUnitarySupportProductStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_unitary_support_product : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (N : Subgroup (HA (AF F) σ J)) {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} {δ : AF F}, IsPlacesIdem T₁ T₂ δ → (∀ w ∈ T₁, ∀ e : AF F, IsPlacesIdem {w} ∅ e → SUSupp σ J e ⊆ N) → (∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → SUSupp σ J e ⊆ N) → SUSupp σ J δ ⊆ N := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.Supp.supp_le_of_single | exact GlobalTheory.CompanionTheory.SaGen.Supp.supp_le_of_single | (intros; apply GlobalTheory.CompanionTheory.SaGen.Supp.supp_le_of_single <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictMonoSnocPermEqSuccAboveStatement
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictMono_snoc_perm_eq_succAbove : ∀ {n : ℕ} (I : Fin n → Fin (n + 1)) (k : Fin (n + 1)) (π : Equiv.Perm (Fin (n + 1))), StrictMono I →
    Fin.snoc (α := fun _ => Fin (n + 1)) I k = ⇑π → I = k.succAbove := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.SnocPerm.eq_succAbove_of_snoc_eq_perm | exact GlobalTheory.CompanionTheory.ConeLocal.SnocPerm.eq_succAbove_of_snoc_eq_perm | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.SnocPerm.eq_succAbove_of_snoc_eq_perm <;> assumption)
end

