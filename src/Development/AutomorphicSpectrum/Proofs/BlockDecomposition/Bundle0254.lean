import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0247
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneNotMemFilOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterInducedTiedSix
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.DeRhamChar

open Module GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime]

theorem exists_inv_fil (a : ℤ) (x : Formalism.Per6.BdR l) (h1 : x ∈ Formalism.Per6.FilD l a) (h2 : x ∉ Formalism.Per6.FilD l (a + 1)) :
    ∃ y ∈ Formalism.Per6.FilD l (-a), x * y = 1 := by
  have hϖ := IsPerfectoidField.maximalIdeal_eq_span_varpi ℂ_[l] l
  have hne := IsPerfectoidField.algebraMap_ne_zero_of_maximalIdeal_eq_span hϖ
  obtain ⟨b, rfl⟩ := (IsPerfectoidField.mem_fil_iff hϖ).1 h1
  have hb : IsUnit b := by
    by_contra hb
    have hm : b ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 hb
    rw [hϖ, Ideal.mem_span_singleton] at hm
    obtain ⟨c, rfl⟩ := hm
    refine h2 ((IsPerfectoidField.mem_fil_iff hϖ).2 ⟨c, ?_⟩)
    rw [map_mul, zpow_add₀ hne, zpow_one, mul_assoc]
  obtain ⟨u, rfl⟩ := hb
  refine ⟨_, (IsPerfectoidField.mem_fil_iff hϖ).2 ⟨((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l), rfl⟩, ?_⟩
  have h3 : algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (u : Formalism.Per6.BdRp l) *
      algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) ((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h4 := mul_inv_cancel₀ (zpow_ne_zero a hne)
  rw [zpow_neg]
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (u : Formalism.Per6.BdRp l) = A at *
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) ((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l) = A' at *
  generalize (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (IsPerfectoidField.varpi ℂ_[l] l) ^ a)⁻¹ = C at *
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (IsPerfectoidField.varpi ℂ_[l] l) ^ a = D at *
  linear_combination (A * A') * h4 + h3

theorem exists_gal (K : FinExt l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] (τ : ↥K.1 →ₐ[ℚ_[l]] LL)
    (σ σ' : LL →ₐ[ℚ_[l]] Om l) (h : σ.comp τ = K.1.val) (h' : σ'.comp τ = K.1.val) :
    ∃ g : ↥(GK K), ∀ x, (g : GQ l) (σ x) = σ' x := by
  letI : Algebra LL (Om l) := σ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] LL (Om l) := .of_algebraMap_eq fun x => (σ.commutes x).symm
  haveI : Normal ℚ_[l] (Om l) := IsAlgClosure.normal ℚ_[l] (Om l)
  let g₀ : Om l →ₐ[ℚ_[l]] Om l := σ'.liftNormal (Om l)
  have hg₀ : ∀ x, g₀ (σ x) = σ' x := fun x => AlgHom.liftNormal_commutes σ' (Om l) x
  let g : GQ l := AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)
  refine ⟨⟨g, ?_⟩, hg₀⟩
  rw [GK, IntermediateField.mem_fixingSubgroup_iff]
  intro c hc
  have h1 : σ (τ ⟨c, hc⟩) = c := DFunLike.congr_fun h ⟨c, hc⟩
  have h2 : σ' (τ ⟨c, hc⟩) = c := DFunLike.congr_fun h' ⟨c, hc⟩
  change g₀ c = c
  rw [← h1, hg₀, h1, h2]

section

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem repE_toGL1 (LL' : FinExt l) (ψ : ↥Gw →* (↥LL'.1)ˣ) (g : ↥(GK Bw.Kw)) (v : Fin 1 → ↥LL'.1) :
    Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) g v = ((ψ (Bw.e.symm g) : (↥LL'.1)ˣ) : ↥LL'.1) • v := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [LocBridge.repE, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, Matrix.mulVec, dotProduct]

theorem card_emb_le (LL' : FinExt l) (hLL : Bw.LL.1 ≤ LL'.1) [Fintype (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1)] :
    Fintype.card (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥Bw.Kw.1 := by
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  rw [← AlgHom.card ℚ_[l] ↥Bw.Kw.1 (Om l)]
  exact Fintype.card_congr
    { toFun := fun τ => LL'.1.val.comp τ
      invFun := fun τ => τ.codRestrict LL'.1.toSubalgebra fun x => hLL (Bw.LL_split τ x)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end

end GlobalTheory.CompanionTheory.DeRhamChar

open GlobalTheory.CompanionTheory.DeRhamChar Module GlobalTheory.Cmp.JumpDict GroundTheory.PAdicHodge in
theorem GlobalTheory.CompanionTheory.DeRhamChar.isdRJ_inv : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ)
      (J : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ),
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ J → PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ⁻¹ (-J) := by
  intro E Ω _ _ _ _ _ l _ P AI hT w A _ O _ _ _ Bw _ LL' hLL ψ J hJ
  obtain ⟨T⟩ := hT
  haveI : IsDomain P.R.BdR := T.eD.toMulEquiv.isDomain (Formalism.Per6.BdR l)
  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have hOm : ∀ x : Om l, algebraMap (Om l) P.R.BdR x ∈ (P.PD Bw.Kw).Fil 0 := fun x => by
    obtain ⟨y, hy, -⟩ := T.om x
    rw [T.fil, hy]
    exact (IsPerfectoidField.mem_fil_iff (IsPerfectoidField.maximalIdeal_eq_span_varpi ℂ_[l] l)).2
      ⟨y, by simp⟩
  have hval : ∀ (a : ℤ) (x : P.R.BdR), x ∈ (P.PD Bw.Kw).Fil a → x ∉ (P.PD Bw.Kw).Fil (a + 1) →
      ∃ y ∈ (P.PD Bw.Kw).Fil (-a), x * y = 1 := fun a x h1 h2 => by
    obtain ⟨y, hy, hxy⟩ := exists_inv_fil a (T.eD x) ((T.fil _ _ _).1 h1) (fun h => h2 ((T.fil _ _ _).2 h))
    refine ⟨T.eD.symm y, (T.fil _ _ _).2 (by simpa using hy), T.eD.injective ?_⟩
    simpa using hxy
  have hmult : ∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) a,
      multV (P.PD Bw.Kw) (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ⁻¹)) τ a = if a = -J τ then 1 else 0 :=
    fun τ a => multV_inv (P.PD Bw.Kw) (GK Bw.Kw).subtype Bw.Kw.1.val (fun _ => rfl)
      (fun g x => by rw [P.PD_actdR]; exact P.actQdR_Om _ x)
      (fun g c => (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 c c.2) hOm hval
      (χ := ψ.comp Bw.e.symm.toMonoidHom) (χ' := ψ⁻¹.comp Bw.e.symm.toMonoidHom)
      (fun g v => repE_toGL1 Bw LL' ψ g v) (fun g v => repE_toGL1 Bw LL' ψ⁻¹ g v)
      (fun g => by simp) τ
      (fun σ σ' h h' => exists_gal Bw.Kw τ σ σ' h h') (J τ) (fun a => hJ.2 τ a) a
  refine ⟨?_, fun τ a => hmult τ a⟩
  have := finrank_ddR_of_one_jump (P.PD Bw.Kw) (card_emb_le Bw LL' hLL)
    (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ⁻¹)) (fun τ => ⟨-J τ, hmult τ⟩)
  simpa [LocBridge.IsdRE] using this
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedObjPdPow
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedFil

theorem exists_lift {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    {δ : DividedPowers J} {δ' : DividedPowers J'} {f : B →+* B'} (hf : IsDPMorphism δ δ' f)
    (hJ : J' = J.map f) (hs : Function.Surjective f) (l : List (ℕ × B')) (hl : ∀ q ∈ l, q.2 ∈ J') :
    ∃ l' : List (ℕ × B), (∀ q ∈ l', q.2 ∈ J) ∧ l'.map Prod.fst = l.map Prod.fst ∧
      (l.map fun q => δ'.dpow q.1 q.2).prod = f (l'.map fun q => δ.dpow q.1 q.2).prod := by
  induction l with
  | nil => exact ⟨[], by simp, rfl, by simp⟩
  | cons q l ih =>
    obtain ⟨l', h1, h2, h3⟩ := ih fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have hq := hl q List.mem_cons_self
    rw [hJ] at hq
    obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective f hs).1 hq
    refine ⟨(q.1, y) :: l', ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      exacts [hy, h1 p hp]
    · simp [h2]
    · simp only [List.map_cons, List.prod_cons, map_mul, h3, ← e]
      rw [hf.2 y hy]

theorem dividedPowerFiltration_le_map {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    {δ : DividedPowers J} {δ' : DividedPowers J'} {f : B →+* B'} (hf : IsDPMorphism δ δ' f)
    (hJ : J' = J.map f) (hs : Function.Surjective f) (r : ℕ) : pdP δ' r ≤ (pdP δ r).map f := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hr, rfl⟩
  obtain ⟨l', h1, h2, h3⟩ := exists_lift hf hJ hs l hl
  rw [h3]
  exact Ideal.mem_map_of_mem f (Ideal.subset_span ⟨l', h1, by rwa [h2], rfl⟩)

section
variable {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ]
  {I : Ideal A} {γ : DividedPowers I} {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  (d : RedIn δ κ γ l n) {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {s : ℕ}

theorem redObj_pdPow (T : Thick (nlFun γ 0 X q (κA O I))) (h : TF l s T) (r : ℕ) :
    (redObj T d h).pdPow r ≤ (T.pdPow r).map (Ideal.Quotient.mk (lnT T l n)) :=
  dividedPowerFiltration_le_map (redδ_dp T h n) rfl Ideal.Quotient.mk_surjective r
end

def toSomeP {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : ℤ) (c : b.R) (j : ℕ) :
    HM Q none c j →ₗ[b.R] HM Q (some r) c j :=
  (sqLe (a := IdF.top _) (a' := IdF.top _) (b := stdI Q none c) (b' := stdI Q (some r) c)
    (fun _ => le_rfl) (fun T => sup_le_sup_right (bot_le : (⊥ : Ideal _) ≤ _) _)).pull j

end GlobalTheory.CompanionTheory.RedFil

namespace GlobalTheory.CompanionTheory.RedFil

section
variable {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ]
  {I : Ideal A} {γ : DividedPowers I} {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  (d : RedIn δ κ γ l n) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ)
  (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
  (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))

theorem val_zero (r : ℕ) (T : (TS γ q l s 𝒱).FullSubcategory) (v : ((redG q s d 𝒱).obj T).B)
    (hv : v ∈ ((redG q s d 𝒱).obj T).pdPow r) :
    (sqLe (a := IdF.top _) (a' := IdF.top _) (b := stdI (TS γ q l s 𝒱) none ((l : A) ^ n))
      (b' := stdI (TS γ q l s 𝒱) (some (r : ℤ)) ((l : A) ^ n)) (fun _ => le_rfl)
      (fun T => sup_le_sup_right (bot_le : (⊥ : Ideal _) ≤ _) _)).τ T
      ((redMor q s d 𝒱 c lam hc none).τ T v) = 0 := by
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
    (redObj_pdPow d T.obj T.property.1 r hv)
  refine Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left ?_))
  change y ∈ T.obj.pdPow (r : ℤ).toNat
  simpa using hy

theorem red_kills (r j : ℕ) : ∀ x ∈ (B.pdS (nlFun δ l X q κ) c r).img j,
    toSomeP (TS γ q l s 𝒱) (r : ℤ) ((l : A) ^ n) j ((redMor q s d 𝒱 c lam hc none).pull j x) = 0 := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 y
  let S := B.pdS (nlFun δ l X q κ) c r
  let m := redMor q s d 𝒱 c lam hc none
  let t := sqLe (a := IdF.top _) (a' := IdF.top _) (b := stdI (TS γ q l s 𝒱) none ((l : A) ^ n))
      (b' := stdI (TS γ q l s 𝒱) (some (r : ℤ)) ((l : A) ^ n)) (fun _ => le_rfl)
      (fun T => sup_le_sup_right (bot_le : (⊥ : Ideal _) ≤ _) _)
  have h1 : CH.d _ j (S.inc.pullC j a) = 0 := by
    rw [S.inc.d_pullC]
    exact (congrArg _ ha).trans (map_zero _)
  have h2 : CH.d _ j (m.pullC j (S.inc.pullC j a)) = 0 := by
    rw [m.d_pullC, h1, map_zero]
  have h3 : CH.d _ j (t.pullC j (m.pullC j (S.inc.pullC j a))) = 0 := by
    rw [t.d_pullC, h2, map_zero]
  have e1 : S.inc.pull j ((CH.cx _).cls a ha) = (CH.cx _).cls (S.inc.pullC j a) h1 :=
    CrystallineSemistableComparison.P.mapH_cls S.inc.hom j a ha h1
  have e2 : m.pull j ((CH.cx _).cls (S.inc.pullC j a) h1) = (CH.cx _).cls (m.pullC j (S.inc.pullC j a)) h2 :=
    CrystallineSemistableComparison.P.mapH_cls m.hom j _ h1 h2
  have e3 : t.pull j ((CH.cx _).cls (m.pullC j (S.inc.pullC j a)) h2) =
      (CH.cx _).cls (t.pullC j (m.pullC j (S.inc.pullC j a))) h3 :=
    CrystallineSemistableComparison.P.mapH_cls t.hom j _ h2 h3
  have e4 : t.pullC j (m.pullC j (S.inc.pullC j a)) = 0 := by
    funext σ
    exact val_zero d q s 𝒱 c lam hc r _ _ (a (((σ ⋙ t.G) ⋙ m.G) ⋙ S.inc.G)).2
  change t.pull j (m.pull j (S.inc.pull j _)) = 0
  rw [e1, e2, e3]
  exact ((CrystallineSemistableComparison.P.cls_surj _ j).2.1 _ h3).2 (by rw [e4]; exact Submodule.zero_mem _)
end

end GlobalTheory.CompanionTheory.RedFil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralOfEpsteinConv
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.ZetaAlongK

open PositivityTheory.RgEis PositivityTheory.RgEis.MG GroundTheory.Global GroundTheory.Automorphic

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem firstCountable_gl : FirstCountableTopology (GL ι 𝔸[k]) := by
  have h1 : SecondCountableTopology (Matrix ι ι 𝔸[k]) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → 𝔸[k]))
  have h2 : SecondCountableTopology (Matrix ι ι 𝔸[k])ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix ι ι 𝔸[k])).symm.isEmbedding.secondCountableTopology
  have h3 : SecondCountableTopology (GL ι 𝔸[k]) :=
    (Units.isEmbedding_embedProduct (M := Matrix ι ι 𝔸[k])).secondCountableTopology
  infer_instance

theorem differentiableAt_globalZeta_of_majorant {F : 𝔸[k] → ℂ} (hFc : Continuous F)
    (χ : HeckeCharacter k) {s₀ : ℂ} {δ : ℝ} (hδ : 0 < δ) {f₀ f₁ f₂ : IdeleGroup k → ℝ}
    (i₀ : Integrable f₀ (ideleMeasure k)) (i₁ : Integrable f₁ (ideleMeasure k))
    (i₂ : Integrable f₂ (ideleMeasure k))
    (b₀ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ s₀.re ≤ f₀ t)
    (b₁ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ (s₀.re - 2 * δ) ≤ f₁ t)
    (b₂ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ (s₀.re + 2 * δ) ≤ f₂ t) :
    DifferentiableAt ℂ (globalZeta F χ) s₀ := by
  have hT : ∀ x : IdeleGroup k, 0 < (IdeleGroup.ideleModule k x : ℝ) :=
    fun x ↦ (IdeleGroup.ideleModule k x).2
  set G : ℂ → IdeleGroup k → ℂ := fun s x ↦
    F x * (χ.toIdele x : ℂ) * ((IdeleGroup.ideleModule k x : ℝ) : ℂ) ^ s with hG
  set G' : ℂ → IdeleGroup k → ℂ :=
    fun s x ↦ G s x * Complex.log (IdeleGroup.ideleModule k x : ℝ) with hG'
  set bound : IdeleGroup k → ℝ := fun x ↦ (f₁ x + f₂ x) / δ with hbound
  have hbound_int : Integrable bound (ideleMeasure k) := (i₁.add i₂).div_const δ
  have hcont' : Continuous (G' s₀) :=
    (continuous_zetaIntegrand hFc χ s₀).mul
      ((Complex.continuous_ofReal.comp continuous_ideleModule_val).clog
        fun x ↦ Complex.ofReal_mem_slitPlane.2 (hT x))
  have hint₀ : Integrable (G s₀) (ideleMeasure k) := by
    refine i₀.mono' (continuous_zetaIntegrand hFc χ s₀).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)
    simp only [hG]
    rw [norm_zetaIntegrand]
    exact b₀ x
  have hle : ∀ x, ∀ s ∈ Metric.ball s₀ δ, ‖G' s x‖ ≤ bound x := by
    intro x s hs
    have hre : |s.re - s₀.re| < δ := by
      have := (Complex.abs_re_le_norm (s - s₀)).trans_lt (mem_ball_iff_norm.1 hs)
      rwa [Complex.sub_re] at this
    have hnorm : ‖G' s x‖ = ‖F x‖ * ((IdeleGroup.ideleModule k x : ℝ) ^ s.re *
        |Real.log (IdeleGroup.ideleModule k x : ℝ)|) := by
      simp only [hG', hG]
      rw [norm_mul, norm_zetaIntegrand, ← Complex.ofReal_log (hT x).le, Complex.norm_real,
        Real.norm_eq_abs, mul_assoc]
    rw [hnorm]
    calc ‖F x‖ * ((IdeleGroup.ideleModule k x : ℝ) ^ s.re * |Real.log (IdeleGroup.ideleModule k x : ℝ)|)
        ≤ ‖F x‖ * (((IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re - 2 * δ) +
            (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re + 2 * δ)) / δ) :=
          mul_le_mul_of_nonneg_left (rpow_mul_abs_log_le (hT x) hδ hre) (norm_nonneg _)
      _ = (‖F x‖ * (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re - 2 * δ) +
            ‖F x‖ * (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re + 2 * δ)) / δ := by ring
      _ ≤ bound x := div_le_div_of_nonneg_right (add_le_add (b₁ x) (b₂ x)) hδ.le
  have hdiff : ∀ x, ∀ s ∈ Metric.ball s₀ δ, HasDerivAt (fun s ↦ G s x) (G' s x) s := by
    intro x s _
    have h := ((Complex.hasStrictDerivAt_const_cpow (y := s)
      (Or.inl (Complex.ofReal_ne_zero.2 (hT x).ne'))).hasDerivAt).const_mul
        (F x * (χ.toIdele x : ℂ))
    refine h.congr_deriv ?_
    simp only [hG', hG]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ideleMeasure k) (F := G)
    (F' := G') (x₀ := s₀) (bound := bound) (Metric.ball_mem_nhds s₀ hδ)
    (Eventually.of_forall fun s ↦ (continuous_zetaIntegrand hFc χ s).aestronglyMeasurable)
    hint₀ hcont'.aestronglyMeasurable
    (Eventually.of_forall fun x s hs ↦ hle x s hs) hbound_int
    (Eventually.of_forall fun x s hs ↦ hdiff x s hs)
  exact key.2.differentiableAt

def col (m : GL ι 𝔸[k]) (i : ι) : ι → 𝔸[k] := (m : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i 1

theorem continuous_col (i : ι) : Continuous fun m : GL ι 𝔸[k] => col m i :=
  (Units.continuous_val (M := Matrix ι ι 𝔸[k])).matrix_mulVec continuous_const

theorem continuous_line {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (x : ι → 𝔸[k]) :
    Continuous fun t : 𝔸[k] => Ψ (t • x) :=
  hΨ.comp (continuous_id.smul continuous_const)

def Maj (Ψ : (ι → 𝔸[k]) → ℂ) (i : ι) (C : Set (GL ι 𝔸[k])) : Prop :=
  ∀ a b : ℝ, 1 < a → ∃ f : IdeleGroup k → ℝ, Integrable f (ideleMeasure k) ∧
    ∀ x : ℝ, a ≤ x → x ≤ b → ∀ m ∈ C, ∀ t : IdeleGroup k,
      ‖Ψ ((t : 𝔸[k]) • col m i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ≤ f t

theorem differentiableOn_lineZeta {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) {m : GL ι 𝔸[k]} (hm : m ∈ C) :
    DifferentiableOn ℂ (fun s => lineZeta Ψ ω s (col m i)) {s | 1 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 1 < s₀.re := hs₀
  set δ := (s₀.re - 1) / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨f₀, i₀, b₀⟩ := h s₀.re s₀.re hs₀'
  obtain ⟨f₁, i₁, b₁⟩ := h (s₀.re - 2 * δ) (s₀.re - 2 * δ) (by rw [hδdef]; linarith)
  obtain ⟨f₂, i₂, b₂⟩ := h (s₀.re + 2 * δ) (s₀.re + 2 * δ) (by linarith)
  exact (differentiableAt_globalZeta_of_majorant (F := fun t => Ψ (t • col m i))
    (continuous_line hΨ _) ω hδ i₀ i₁ i₂ (fun t => b₀ _ le_rfl le_rfl m hm t)
    (fun t => b₁ _ le_rfl le_rfl m hm t) (fun t => b₂ _ le_rfl le_rfl m hm t)).differentiableWithinAt

theorem norm_lineZeta_le {Ψ : (ι → 𝔸[k]) → ℂ} (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} {f : IdeleGroup k → ℝ} {a b : ℝ} (hf : Integrable f (ideleMeasure k))
    (h : ∀ x : ℝ, a ≤ x → x ≤ b → ∀ m ∈ C, ∀ t : IdeleGroup k,
      ‖Ψ ((t : 𝔸[k]) • col m i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ≤ f t)
    {s : ℂ} (h1 : a ≤ s.re) (h2 : s.re ≤ b) {m : GL ι 𝔸[k]} (hm : m ∈ C) :
    ‖lineZeta Ψ ω s (col m i)‖ ≤ ∫ t, f t ∂ideleMeasure k := by
  refine norm_integral_le_of_norm_le hf (Eventually.of_forall fun t => ?_)
  rw [norm_zetaIntegrand (fun a => Ψ (a • col m i)) ω s t]
  exact h _ h1 h2 m hm t

def ig (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (i : ι) (y : ℂ × GL ι 𝔸[k]) (t : IdeleGroup k) : ℂ :=
  Ψ ((t : 𝔸[k]) • col y.2 i) * (ω.toIdele t : ℂ) * ((IdeleGroup.ideleModule k t : ℝ) : ℂ) ^ y.1

theorem norm_ig (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (i : ι) (y : ℂ × GL ι 𝔸[k]) (t : IdeleGroup k) :
    ‖ig Ψ ω i y t‖ = ‖Ψ ((t : 𝔸[k]) • col y.2 i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ y.1.re :=
  norm_zetaIntegrand (fun a => Ψ (a • col y.2 i)) ω y.1 t

theorem continuous_ig {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k) (i : ι)
    (y : ℂ × GL ι 𝔸[k]) : Continuous (ig Ψ ω i y) :=
  continuous_zetaIntegrand (continuous_line hΨ (col y.2 i)) ω y.1

theorem continuous_ig_param {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k) (i : ι)
    (t : IdeleGroup k) : Continuous fun y : ℂ × GL ι 𝔸[k] => ig Ψ ω i y t := by
  have c1 : Continuous fun y : ℂ × GL ι 𝔸[k] => Ψ ((t : 𝔸[k]) • col y.2 i) :=
    hΨ.comp ((continuous_const : Continuous fun _ : ℂ × GL ι 𝔸[k] => (t : 𝔸[k])).smul
      ((continuous_col i).comp continuous_snd))
  refine (c1.mul continuous_const).mul ?_
  exact continuous_fst.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule k t).2.ne'))

theorem eventually_near {C : Set (GL ι 𝔸[k])} {s₀ : ℂ} {m₀ : GL ι 𝔸[k]} {a b : ℝ} (ha : a < s₀.re)
    (hb : s₀.re < b) : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝[{s | 1 < s.re} ×ˢ C] (s₀, m₀),
      a ≤ y.1.re ∧ y.1.re ≤ b ∧ y.2 ∈ C := by
  have hc : Continuous fun y : ℂ × GL ι 𝔸[k] => y.1.re := Complex.continuous_re.comp continuous_fst
  have e1 : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝 (s₀, m₀), a < y.1.re :=
    hc.continuousAt.eventually (lt_mem_nhds ha)
  have e2 : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝 (s₀, m₀), y.1.re < b :=
    hc.continuousAt.eventually (gt_mem_nhds hb)
  filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin] with y y1 y2 y3
  exact ⟨y1.le, y2.le, y3.2⟩

theorem continuousOn_ig {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) :
    ContinuousOn (fun y : ℂ × GL ι 𝔸[k] => ∫ t, ig Ψ ω i y t ∂ideleMeasure k)
      ({s | 1 < s.re} ×ˢ C) := by
  have := firstCountable_gl (k := k) (ι := ι)
  rintro ⟨s₀, m₀⟩ ⟨hs₀, hm₀⟩
  have hs₀' : 1 < s₀.re := hs₀
  obtain ⟨f, hf, hb⟩ := h ((1 + s₀.re) / 2) (s₀.re + 1) (by linarith)
  have hnear := eventually_near (C := C) (m₀ := m₀) (s₀ := s₀) (a := (1 + s₀.re) / 2) (b := s₀.re + 1)
    (by linarith) (by linarith)
  refine continuousWithinAt_of_dominated (bound := f) ?_ ?_ hf ?_
  · exact Eventually.of_forall fun y => (continuous_ig hΨ ω i y).aestronglyMeasurable
  · filter_upwards [hnear] with y hy
    refine Eventually.of_forall fun t => ?_
    rw [norm_ig]
    exact hb _ hy.1 hy.2.1 _ hy.2.2 t
  · exact Eventually.of_forall fun t => (continuous_ig_param hΨ ω i t).continuousWithinAt

theorem continuousOn_lineZeta {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) :
    ContinuousOn (fun y : ℂ × GL ι 𝔸[k] => lineZeta Ψ ω y.1 (col y.2 i))
      ({s | 1 < s.re} ×ˢ C) :=
  continuousOn_ig hΨ ω h

theorem zt_eq {G : Type} [Group G] (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι)
    (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (g : G) :
    zt π d i Ψ ω s g = lineZeta Ψ ω s (col (kap π d g)⁻¹ i) := rfl

theorem zetaK : EpConv → ZetaK := by
  intro hE G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hS Ψ hΨ
  have hΨc : Continuous Ψ := GJMatrix.continuous_of_mem_schwartzBruhatPi hΨ
  have hcont : Continuous fun g : G => (kap π d g)⁻¹ :=
    ((continuous_const.mul hS.cont).mul continuous_const).inv
  have hC : IsCompact ((fun g : G => (kap π d g)⁻¹) '' (K : Set G)) := hK.image hcont
  have hM : Maj Ψ i ((fun g : G => (kap π d g)⁻¹) '' (K : Set G)) :=
    fun a b ha => (hE k ι Ψ hΨ).1 i a b _ ha hC
  have hmem : ∀ κ : K, (kap π d κ)⁻¹ ∈ (fun g : G => (kap π d g)⁻¹) '' (K : Set G) :=
    fun κ => ⟨κ, κ.2, rfl⟩
  refine ⟨fun κ => differentiableOn_lineZeta hΨc ω hM (hmem κ), ?_, ?_⟩
  · have hmap : Continuous fun y : ℂ × K => (y.1, (kap π d (y.2 : G))⁻¹) :=
      continuous_fst.prodMk (hcont.comp (continuous_subtype_val.comp continuous_snd))
    have hS' : Set.MapsTo (fun y : ℂ × K => (y.1, (kap π d (y.2 : G))⁻¹))
        ({s : ℂ | 1 < s.re} ×ˢ Set.univ)
        ({s : ℂ | 1 < s.re} ×ˢ ((fun g : G => (kap π d g)⁻¹) '' (K : Set G))) :=
      fun y hy => ⟨hy.1, hmem y.2⟩
    have h2 := ContinuousOn.comp (continuousOn_lineZeta hΨc ω hM) hmap.continuousOn hS'
    exact h2.congr fun y _ => zt_eq π d i Ψ ω y.1 y.2
  · intro a b ha
    obtain ⟨f, hf, hb⟩ := (hE k ι Ψ hΨ).1 i a b _ ha hC
    exact ⟨∫ t, f t ∂ideleMeasure k, fun s h1 h2 κ => norm_lineZeta_le ω hf hb h1 h2 (hmem κ)⟩

end GlobalTheory.CompanionTheory.ZetaAlongK
end
end

