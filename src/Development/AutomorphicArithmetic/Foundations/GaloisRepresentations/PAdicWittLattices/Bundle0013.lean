import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
import Formalism.LocalToGlobal.CyclotomicLocalNorms.AddValuationAlgebraMapPadicIntUnitEqZero
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JJumpOfHT2
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

namespace UpperTheory.Gal.G3

private theorem eig_coord {F : Type} [Field F] {m : ℕ} (s : F →+* F) (A : Matrix (Fin m) (Fin m) F)
    (Q : Matrix.GeneralLinearGroup (Fin m) F) (D : Fin m → F) (z : Fin m → F) (u : F)
    (h1 : A * (Q : Matrix (Fin m) (Fin m) F).map s = (Q : Matrix (Fin m) (Fin m) F) * Matrix.diagonal D)
    (h2 : A.mulVec (fun q => s (z q)) = u • z) (i : Fin m) :
    D i * s (((Q⁻¹ : Matrix.GeneralLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F).mulVec z i) =
      u * ((Q⁻¹ : Matrix.GeneralLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F).mulVec z i := by
  set Qi : Matrix (Fin m) (Fin m) F := ((Q⁻¹ : Matrix.GeneralLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) with hQi
  set Qm : Matrix (Fin m) (Fin m) F := (Q : Matrix (Fin m) (Fin m) F) with hQm
  have hQ1 : Qm * Qi = 1 := by
    rw [hQi, hQm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQ2 : Qi * Qm = 1 := by
    rw [hQi, hQm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set c : Fin m → F := Qi.mulVec z with hc
  have hz : Qm.mulVec c = z := by
    rw [hc, Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec]
  have hsz : (fun q => s (z q)) = (Qm.map s).mulVec (fun q => s (c q)) := by
    funext q
    rw [← hz]
    exact RingHom.map_mulVec s Qm c q
  have key : Qm.mulVec ((Matrix.diagonal D).mulVec (fun q => s (c q))) = Qm.mulVec (u • c) := by
    rw [Matrix.mulVec_mulVec, ← h1, ← Matrix.mulVec_mulVec, ← hsz, h2, Matrix.mulVec_smul, hz]
  have key2 : (Matrix.diagonal D).mulVec (fun q => s (c q)) = u • c := by
    have h3 : ∀ v : Fin m → F, Qi.mulVec (Qm.mulVec v) = v := fun v => by
      rw [Matrix.mulVec_mulVec, hQ2, Matrix.one_mulVec]
    rw [← h3 ((Matrix.diagonal D).mulVec fun q => s (c q)), key, h3]
  have := congrFun key2 i
  simpa [Matrix.mulVec_diagonal] using this

private theorem chi_solve {l : ℕ} [Fact l.Prime] (t : ℚ_[l]ˣ) (n b : ℤ) (x y : ℂ_[l])
    (h : (((t ^ (-n) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * y = (((t ^ (-b) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x) :
    y = (((t ^ (n - b) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x := by
  have e : ∀ u v : ℚ_[l]ˣ, (((u * v : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = ((u : ℚ_[l]) : ℂ_[l]) * ((v : ℚ_[l]) : ℂ_[l]) :=
    fun u v => by rw [Units.val_mul]; exact map_mul (algebraMap ℚ_[l] ℂ_[l]) _ _
  have one : (((1 : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = 1 := by
    rw [Units.val_one]; exact map_one (algebraMap ℚ_[l] ℂ_[l])
  calc y = (((t ^ n * t ^ (-n) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * y := by
        rw [← zpow_add, add_neg_cancel, zpow_zero, one, one_mul]
    _ = (((t ^ n : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * ((((t ^ (-n) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * y) := by
        rw [e, mul_assoc]
    _ = (((t ^ n : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * ((((t ^ (-b) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x) := by rw [h]
    _ = (((t ^ (n - b) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x := by
        rw [← mul_assoc, ← e, ← zpow_add, sub_eq_add_neg]

private theorem gal_cont {l : ℕ} [Fact l.Prime] (g : GQ l) : Continuous fun x : Om l => g x := by
  refine (AddMonoidHomClass.isometry_of_norm g fun x => ?_).continuous
  have h := GlobalTheory.RingBasics.norm_σC g (x : ℂ_[l])
  rw [GlobalTheory.RingBasics.σC_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe] at h
  exact h

private theorem chiPow_eq {l : ℕ} [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (n : ℤ) :
    GlobalTheory.HTLink.chiPow σ n = ((((P.χQ σ) ^ n : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) := by
  have hχ : P.χQ = Formalism.L2.LocGap.Gal.χQ l := Formalism.L2.LocGap.Gal.eq_χQ_of_cyc P.χQ P.χQ_cyc
  rw [GlobalTheory.HTLink.chiPow, hχ, Units.val_zpow_eq_zpow_val]
  exact (map_zpow₀ (algebraMap ℚ_[l] ℂ_[l]) _ n).symm

end UpperTheory.Gal.G3

set_option maxHeartbeats 1000000 in

theorem UpperTheory.Gal.G3.jJumpOfHT2 :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.JumpOfHT2 := by
  classical
  unfold PositivityTheory.AutomorphicGaloisHodgeTate.G8.JumpOfHT2
  intro E Ω _ _ _ _ _ l _ P AI hT' Gw O O' _ _ _ _ _ _ Bw Bw' γ hC d r a Jm hOcc hJ
  obtain ⟨hT⟩ := hT'
  obtain ⟨LL', r', ⟨hLL, hmod⟩, hdR, τ', hInd, hcnt⟩ := hJ
  obtain ⟨S, z, hz0, hz⟩ := hOcc
  haveI := Bw.Kw.2
  haveI := Bw'.Kw.2
  haveI := LL'.2

  have hg : ∀ y : ↥Bw.Kw.1, γ (y : Om l) = ((τ' y : ↥LL'.1) : Om l) := by
    let τo : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l := LL'.1.val.comp τ'
    let g₁ : GQ l := AlgEquiv.ofBijective (τo.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _)
    have hg₁ : ∀ y : ↥Bw.Kw.1, g₁ (y : Om l) = ((τ' y : ↥LL'.1) : Om l) := fun y =>
      τo.liftNormal_commutes (Om l) y
    have hclosed : IsClosed {x : Om l | g₁ x = γ x} := isClosed_eq (gal_cont g₁) (gal_cont γ)
    have hsub : Set.range (fun x : E => Bw.j (algebraMap E Ω x)) ⊆ {x : Om l | g₁ x = γ x} := by
      rintro _ ⟨x, rfl⟩
      calc g₁ (Bw.j (algebraMap E Ω x)) = ((τ' ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ : ↥LL'.1) : Om l) :=
            hg₁ ⟨_, Bw.j_E x⟩
        _ = Bw'.j (algebraMap E Ω x) := (hInd x).symm
        _ = γ (Bw.j (algebraMap E Ω x)) := hC.1 _
    intro y
    rw [← hg₁ y]
    exact ((hclosed.closure_subset_iff.2 hsub) (Bw.j_dense y.2)).symm

  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : FinExt l, K₁.1 = Bw.Kw.1.map (γ : Om l →ₐ[ℚ_[l]] Om l) :=
    ⟨⟨Bw.Kw.1.map (γ : Om l →ₐ[ℚ_[l]] Om l),
      LinearEquiv.finiteDimensional (IntermediateField.equivMap Bw.Kw.1 (γ : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩
  have hK : ∀ x, x ∈ Bw.Kw.1 ↔ γ x ∈ K₁.1 := GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₁
  have hK₁LL : K₁.1 ≤ LL'.1 := by
    rw [hK₁]
    rintro _ ⟨x, hx, rfl⟩
    change γ x ∈ LL'.1
    rw [show γ x = _ from hg ⟨x, hx⟩]
    exact (τ' ⟨x, hx⟩).2

  let cj : ↥(GK K₁) →* ↥(GK Bw.Kw) :=
    { toFun := fun h => ⟨γ⁻¹ * (h : GQ l) * γ, GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK h.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun h₁ h₂ => Subtype.ext (by simp [mul_assoc]) }
  let r₁ : ↥(GK K₁) →* Matrix.GeneralLinearGroup (Fin d) ↥LL'.1 :=
    (r'.comp Bw.e.symm.toMonoidHom).comp cj
  have hρ : ∀ (h : ↥(GK Bw.Kw)) (h' : ↥(GK K₁)), (h' : GQ l) = γ * h * γ⁻¹ →
      (((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
        ((Units.coeHom _).comp r₁)) h' = Bw.repE LL' r' h := by
    intro h h' hh
    have : cj h' = h := Subtype.ext (by simp [cj, hh, mul_assoc])
    simp only [MonoidHom.comp_apply, r₁, this]
    rfl
  have hD := GlobalTheory.Pst.BridgeInd.finrank_DdR_conj P hρ hK
  have hdR₁ : Module.finrank ↥LL'.1 ↥(DdR (P.PD K₁) (LL := ↥LL'.1) (V := Fin d → ↥LL'.1)
      (((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
        ((Units.coeHom _).comp r₁))) = Module.finrank ℚ_[l] ↥K₁.1 * d := by
    rw [← hD, ← GlobalTheory.Pst.BridgeInd.finrank_eq_of_mem_iff_field hK]
    exact hdR
  let τ₂ : ↥K₁.1 →ₐ[ℚ_[l]] ↥LL'.1 := IntermediateField.inclusion hK₁LL
  have hτ₂ : ∀ x : ↥K₁.1, ((τ₂ x : ↥LL'.1) : Om l) = (x : Om l) := fun x => rfl
  have hM : ∀ n, multV (P.PD Bw.Kw) (Bw.repE LL' r') τ' n = multV (P.PD K₁) _ τ₂ n :=
    fun n => GlobalTheory.Pst.BridgeInd.multV_conj P hρ hK τ' τ₂ (fun c c' hc => Subtype.ext (by
      change (c' : Om l) = _; rw [hc, hg])) n
  have hsplit : ∀ (σ : ↥K₁.1 →ₐ[ℚ_[l]] Om l) (x : ↥K₁.1), σ x ∈ LL'.1 := by
    intro σ x
    have hx : γ⁻¹ (x : Om l) ∈ Bw.Kw.1 := (hK _).2 (by simp)
    let e₁ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥K₁.1 :=
      ((γ : Om l →ₐ[ℚ_[l]] Om l).comp Bw.Kw.1.val).codRestrict K₁.1.toSubalgebra fun c => (hK _).1 c.2
    have he : e₁ ⟨γ⁻¹ (x : Om l), hx⟩ = x := Subtype.ext (by
      change γ (γ⁻¹ (x : Om l)) = (x : Om l)
      rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl)
    rw [← he]
    exact hLL (Bw.LL_split (σ.comp e₁) ⟨γ⁻¹ (x : Om l), hx⟩)
  haveI := K₁.2
  let K₀ : FinExt l := ⟨K₁.1 ⊔ LL'.1, inferInstance⟩
  obtain ⟨Pm, k, hk, heig⟩ := GlobalTheory.T.deRham_exists_hodgeTate_eigenbasis l P AI hT K₁ LL' d r₁ hdR₁ hsplit τ₂ hτ₂ K₀
    le_sup_left le_sup_right
  have hJm : Multiset.map k Finset.univ.val = Jm := by
    refine Multiset.ext.mpr fun n => ?_
    have := (hk n).trans ((hM n).symm.trans (hcnt n).symm)
    exact_mod_cast this

  let F : IntermediateField ℚ_[l] (Om l) := IntermediateField.adjoin ℚ_[l] (S : Set (Om l))
  haveI : FiniteDimensional ℚ_[l] F :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI := K₀.2
  let K'' : FinExt l := ⟨K₀.1 ⊔ Bw'.Kw.1 ⊔ F, inferInstance⟩
  set c : Fin d → ℂ_[l] :=
    ((Pm⁻¹ : Matrix.GeneralLinearGroup (Fin d) ℂ_[l]) : Matrix (Fin d) (Fin d) ℂ_[l]).mulVec z with hc
  have hcoord : ∀ h : GQ l, h ∈ GK K'' → ∀ i,
      ((((P.χQ h) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * Per.σC h (c i) =
        ((((P.χQ h) ^ (-a) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * c i := by
    intro h hh i
    have h0 : h ∈ GK K₀ := GK_le (le_trans le_sup_left le_sup_left) hh
    have hw : h ∈ GK Bw'.Kw := GK_le (le_trans le_sup_right le_sup_left) hh
    have h1 : h ∈ GK K₁ := GK_le le_sup_left h0
    have hS : ∀ x ∈ S, h x = x := fun x hx =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x
        ((le_sup_right : F ≤ K''.1) (IntermediateField.subset_adjoin _ _ hx))
    have hx : Bw'.e.symm ⟨h, hw⟩ = Bw.e.symm (cj ⟨h, h1⟩) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [hC.2, MulEquiv.apply_symm_apply]
      change h = γ * (γ⁻¹ * h * γ) * γ⁻¹
      group
    have e1 : ((r (Bw'.e.symm ⟨h, hw⟩)).val.map (algebraMap (Om l) ℂ_[l])).mulVec (fun q => Per.σC h (z q)) =
        GlobalTheory.HTLink.chiPow h (-a) • z := hz ⟨h, hw⟩ hS
    have e2 := heig ⟨h, h1⟩ h0
    have hr : (r (Bw.e.symm (cj ⟨h, h1⟩))).val.map (algebraMap (Om l) ℂ_[l]) =
        (r₁ ⟨h, h1⟩ : Matrix (Fin d) (Fin d) ↥LL'.1).map (fun x => (((x : ↥LL'.1) : Om l) : ℂ_[l])) := by
      rw [← hmod]
      rfl
    rw [hx, hr, chiPow_eq P] at e1
    exact eig_coord (Per.σC h) _ Pm _ z _ e2 e1 i
  have hc0 : ∃ i, c i ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hz0
    have hc' : c = 0 := funext hall
    have : (Pm : Matrix (Fin d) (Fin d) ℂ_[l]).mulVec c = z := by
      rw [hc, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← this, hc', Matrix.mulVec_zero]
  obtain ⟨i, hi⟩ := hc0
  have hki : k i = a := by
    by_contra hne
    exact hi (GlobalTheory.T.tate_no_twisted_invariants_complexPadic l P AI hT K'' (k i - a) (sub_ne_zero.2 hne) (c i) fun g =>
      UpperTheory.Gal.G3.chi_solve _ _ _ _ _ (hcoord g g.2 i))
  rw [← hJm, ← hki]
  exact Multiset.mem_map_of_mem k (Finset.mem_univ_val i)

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLocalMat
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem isMatF_of_isMat {k : Type} [Field k] {l : ℕ} [Fact l.Prime] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]
    (θ : H.Γ → Formalism.ConjugateSelfDual.Qbar l) {d : ℕ} (ρ₁ : (Ω ≃ₐ[k] Ω) →* Matrix.GeneralLinearGroup (Fin d) (Formalism.ConjugateSelfDual.Qbar l))
    (h : UpperTheory.Gal.Int.Geo.IsMat l H Ω (Formalism.ConjugateSelfDual.Qbar l) θ ρ₁)
    (f : (Ω ≃ₐ[k] Ω) → Matrix (Fin d) (Fin d) (Formalism.ConjugateSelfDual.Qbar l)) (hf : ∀ σ, (ρ₁ σ).val = f σ) :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.IsMatF H Ω θ f := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b, fun σ j => ?_⟩
  rw [hb σ j, hf σ]

theorem UpperTheory.Gal.G3.jLocalMat :
    UpperTheory.Gal.Seam.NiceBc → UpperTheory.Gal.Seam.HopEx → UpperTheory.Gal.Seam.LocTower → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LocalMat := by
  intro hNice hHop hLoc E Ω _ _ _ _ _ l _ H θ hN Gw O _ _ _ Bw τK hτ
  refine ⟨fun g => ⟨_, hHop l _ _ (UpperTheory.Gal.Int.Geo.bcAlong H τK) (hNice _ _ τK H hN) g⟩, ?_⟩
  intro d ρ hρ
  obtain ⟨ρ₁, hρ₁, hc⟩ := hLoc l E _ Ω (Formalism.ConjugateSelfDual.Qbar l) τK Bw.j (fun x => (hτ x).symm) H hN
    (Formalism.ConjugateSelfDual.Qbar l) θ d ρ hρ
  refine isMatF_of_isMat (UpperTheory.Gal.Int.Geo.bcAlong H τK) (Formalism.ConjugateSelfDual.Qbar l) θ ρ₁ hρ₁ _
    (fun σ => congrArg Units.val (hc _ σ (fun x => ?_)))
  rw [← Bw.e_comm]
  erw [MulEquiv.apply_symm_apply]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLowCov
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open NumberField IsDedekindDomain UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
universe u v

private theorem ext2 {X B k K T : Scheme.{0}} {p : X ⟶ B} {g₁ : k ⟶ B} {g₂ : K ⟶ k}
    (a b : T ⟶ pullback (pullback.snd p g₁) g₂)
    (h1 : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _)
    (h2 : a ≫ pullback.fst _ _ ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ ≫ pullback.fst _ _) : a = b := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h2
    · simp only [Category.assoc, pullback.condition]
      rw [reassoc_of% h1]
  · exact h1

private theorem bcComp {B B' X Y Z : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {r : Z ⟶ B'}
    (f₁ : Z ⟶ Y) (f₂ : Y ⟶ X) (h₁ : f₁ ≫ q = r) (h₂ : f₂ ≫ p = q) (h : (f₁ ≫ f₂) ≫ p = r) :
    bcMap g (f₁ ≫ f₂) h = bcMap g f₁ h₁ ≫ bcMap g f₂ h₂ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcMap_fst]
    rw [← Category.assoc (bcMap g f₁ h₁), bcMap_fst, Category.assoc]
  · simp only [Category.assoc, bcMap_snd]

private theorem bcCongr {B B' X Y : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {f f' : Y ⟶ X}
    (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) : bcMap g f h = bcMap g f' h' := by
  subst e; rfl

private theorem square {B B' k K X Y : Scheme.{0}} (gφ : B' ⟶ B) (g₁ : k ⟶ B) (g₂ : K ⟶ k) (gO : K ⟶ B')
    {p : X ⟶ B} {q : Y ⟶ B} (u : Y ⟶ X) (h : u ≫ p = q)
    (eX : pullback (pullback.snd p gφ) gO ⟶ pullback (pullback.snd p g₁) g₂)
    (eY : pullback (pullback.snd q gφ) gO ⟶ pullback (pullback.snd q g₁) g₂)
    (hX1 : eX ≫ pullback.snd _ _ = pullback.snd _ _)
    (hX2 : eX ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _)
    (hY1 : eY ≫ pullback.snd _ _ = pullback.snd _ _)
    (hY2 : eY ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _) :
    bcMap gO (bcMap gφ u h) (bcMap_snd _ _ _) ≫ eX = eY ≫ bcMap g₂ (bcMap g₁ u h) (bcMap_snd _ _ _) := by
  apply ext2
  · simp only [Category.assoc, hX1, hY1, bcMap_snd]
  · simp only [Category.assoc, hX2, reassoc_of% hY2, bcMap_fst, reassoc_of% bcMap_fst]

private theorem modP (hM : ModBc) (l : ℕ) [Fact l.Prime] (K : FinExt l) {O : Type} [CommRing O] [IsNoetherianRing O]
    (φ : O →+* ↥(CrystallineSemistableComparison.OK l K.1)) {Y : Scheme.{0}} (p : Y ⟶ sp O) (d : ℕ)
    (hs : SmoothOfRelativeDimension d p) (hp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver p) :
    (⟨_, pullback.snd p (Spec.map (CommRingCat.ofHom φ))⟩ : CrystallineSemistableComparison.Model l K.1).Sm ∧
      SmoothOfRelativeDimension d (pullback.snd p (Spec.map (CommRingCat.ofHom φ))) := by
  have h : (⟨_, pullback.snd (𝟙 Y ≫ p) (Spec.map (CommRingCat.ofHom φ))⟩ : CrystallineSemistableComparison.Model l K.1).Sm ∧
      SmoothOfRelativeDimension d (pullback.snd (𝟙 Y ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    hM l K φ p d hs hp (𝟙 Y)
  rw [Category.id_comp] at h
  exact h

private theorem galPart (hSp : BcSplits) (hGal : BcGal) {B k K Y T W₀ : Scheme.{0}} (p : Y ⟶ B) (g₁ : k ⟶ B) (g₂ : K ⟶ k)
    (s : T ⟶ Y) [IsFinite s] [Etale s] (c₀ : W₀ ⟶ Y) (G : Type) [Group G] [Finite G] (a₀ : G → (W₀ ⟶ W₀)) (n : ℕ)
    (σ₀ : Fin n → (W₀ ⟶ T)) (hG : IsGalois c₀ G a₀) (hS : Splits s c₀ σ₀) :
    ∃ (ha : ∀ x, a₀ x ≫ c₀ ≫ p = c₀ ≫ p) (hσ : ∀ j, σ₀ j ≫ s ≫ p = c₀ ≫ p)
      (hσ₁ : ∀ j, bcMap g₁ (σ₀ j) (hσ j) ≫ bcMap g₁ s rfl ≫ pullback.snd p g₁ = pullback.snd (c₀ ≫ p) g₁),
      IsGalois (bcMap g₂ (bcMap g₁ c₀ rfl) (bcMap_snd _ _ _)) G
        (fun x => bcMap g₂ (bcMap g₁ (a₀ x) (ha x)) (bcMap_snd _ _ _)) ∧
      Splits (bcMap g₂ (bcMap g₁ s rfl) rfl) (bcMap g₂ (bcMap g₁ c₀ rfl) (bcMap_snd _ _ _))
        (fun j => bcMap g₂ (bcMap g₁ (σ₀ j) (hσ j)) (hσ₁ j)) := by
  have hac := hG.2.2.2.2.2.1
  have hsc := hS.1
  have ha : ∀ x, a₀ x ≫ c₀ ≫ p = c₀ ≫ p := fun x => by rw [← Category.assoc, hac x]
  have hσ : ∀ j, σ₀ j ≫ s ≫ p = c₀ ≫ p := fun j => by rw [← Category.assoc, hsc j]
  have hσ₁ : ∀ j, bcMap g₁ (σ₀ j) (hσ j) ≫ bcMap g₁ s rfl ≫ pullback.snd p g₁ =
      pullback.snd (c₀ ≫ p) g₁ := fun j => by simp only [bcMap_snd]
  refine ⟨ha, hσ, hσ₁, ?_, ?_⟩
  · have hG1 := hGal g₁ p (c₀ ≫ p) c₀ rfl G a₀ ha hG
    exact hGal g₂ (pullback.snd p g₁) (pullback.snd (c₀ ≫ p) g₁) (bcMap g₁ c₀ rfl) (bcMap_snd _ _ _) G _
      (fun x => bcMap_snd _ _ _) hG1
  · obtain ⟨hF, hE, hsp⟩ := hSp g₁ p (s ≫ p) (c₀ ≫ p) s rfl c₀ rfl (Fin n) σ₀ hσ
    haveI := hF
    haveI := hE
    exact (hSp g₂ (pullback.snd p g₁) _ (pullback.snd (c₀ ≫ p) g₁) (bcMap g₁ s rfl) rfl (bcMap g₁ c₀ rfl)
      (bcMap_snd _ _ _) (Fin n) _ hσ₁).2.2 (hsp hS)

private theorem compPart {B k K Y T W₀ : Scheme.{0}} (p : Y ⟶ B) (g₁ : k ⟶ B) (g₂ : K ⟶ k) (s t : T ⟶ Y)
    (ht : t ≫ p = s ≫ p) (c₀ : W₀ ⟶ Y) (σ : W₀ ⟶ T) (hσ : σ ≫ s ≫ p = c₀ ≫ p) (hu : (σ ≫ t) ≫ p = c₀ ≫ p)
    (hσ₁ : bcMap g₁ σ hσ ≫ bcMap g₁ s rfl ≫ pullback.snd p g₁ = pullback.snd (c₀ ≫ p) g₁)
    (ht' : bcMap g₁ t ht ≫ pullback.snd p g₁ = bcMap g₁ s rfl ≫ pullback.snd p g₁) :
    bcMap g₂ (bcMap g₁ (σ ≫ t) hu) (bcMap_snd _ _ _) = bcMap g₂ (bcMap g₁ σ hσ) hσ₁ ≫ bcMap g₂ (bcMap g₁ t ht) ht' := by
  have h' : (bcMap g₁ σ hσ ≫ bcMap g₁ t ht) ≫ pullback.snd p g₁ = pullback.snd (c₀ ≫ p) g₁ := by
    simp only [Category.assoc, ht', hσ₁]
  exact (bcCongr g₂ (bcComp g₁ σ t hσ ht hu) _ h').trans (bcComp g₂ _ _ hσ₁ ht' h')

set_option maxHeartbeats 4000000 in
theorem UpperTheory.Gal.G3.jLowCov :
    GalClosD → BcSplits → BcGal → GenIso → ModBc → LowCov := by
  intro hGC hSp hGal hGI hM E _ _ l _ H θ w C D K τK hτ
  let φ : Ow w →+* CrystallineSemistableComparison.OK l K.1 :=
    RingHom.codRestrict (τK.comp (HeightOneSpectrum.valuation E w).valuationSubring.subtype) _
      (fun x => GroundTheory.PAdicHodge.mem_normInteger.mpr (hτ x))
  have hφ : ∀ x : Ow w, algebraMap (CrystallineSemistableComparison.OK l K.1) K.1 (φ x) = τK (algebraMap (Ow w) E x) := fun x => rfl
  obtain ⟨d₀, hd₀⟩ := C.dim
  obtain ⟨eZ, hZ1, hZ2⟩ := hGI φ τK hφ C.p
  have hMZ := modP hM l K φ C.p d₀ hd₀ C.proj
  refine ⟨⟨_, pullback.snd C.p (Spec.map (CommRingCat.ofHom φ))⟩, eZ,
    ⟨hMZ.1, ⟨d₀, hMZ.2⟩, eZ, hZ1⟩, hZ1, fun g => ?_⟩
  have hfet := D.fet g
  haveI := hfet.1
  haveI := hfet.2.1
  obtain ⟨W₀, c₀, G, _, _, a₀, σ₀, hG, hS⟩ := hGC (D.s g) (D.d g) (D.fet g)
  obtain ⟨ha, hσ, hσ₁, hGal', hSpl⟩ := galPart hSp hGal C.p (gen (Ow w) E)
    (Spec.map (CommRingCat.ofHom τK)) (D.s g) c₀ G a₀ (D.d g) σ₀ hG hS
  haveI := hG.1
  haveI := hG.2.1
  have hMW := hM l K φ C.p d₀ hd₀ C.proj c₀
  obtain ⟨eW, hW1, hW2⟩ := hGI φ τK hφ (c₀ ≫ C.p)
  have hu : ∀ i, (σ₀ i ≫ D.t g) ≫ C.p = c₀ ≫ C.p := fun i => by
    rw [Category.assoc, D.comm g, ← Category.assoc, hS.1 i]
  have ht' : bcMap (gen (Ow w) E) (D.t g) (D.comm g) ≫ pullback.snd C.p (gen (Ow w) E) =
      bcMap (gen (Ow w) E) (D.s g) rfl ≫ pullback.snd C.p (gen (Ow w) E) := by
    simp only [bcMap_snd]
  refine ⟨_, bcMap (Spec.map (CommRingCat.ofHom τK)) (bcMap (gen (Ow w) E) c₀ rfl) (bcMap_snd _ _ _),
    G, inferInstance, inferInstance, _, Fin (D.d g), inferInstance,
    fun i => bcMap (Spec.map (CommRingCat.ofHom τK)) (bcMap (gen (Ow w) E) (σ₀ i) (hσ i)) (hσ₁ i), hGal', ?_,
    ⟨_, pullback.snd (c₀ ≫ C.p) (Spec.map (CommRingCat.ofHom φ))⟩, eW,
    ⟨hMW.1, ⟨d₀, hMW.2⟩, eW, ?_⟩,
    ⟨bcMap (Spec.map (CommRingCat.ofHom φ)) c₀ rfl, bcMap_snd _ _ _, ?_⟩,
    fun i => ⟨bcMap (Spec.map (CommRingCat.ofHom φ)) (σ₀ i ≫ D.t g) (hu i), bcMap_snd _ _ _, ?_⟩⟩
  · exact hSpl
  · exact (congrArg (eW.hom ≫ ·) (bcMap_snd _ _ _)).trans hW1
  · exact square (Spec.map (CommRingCat.ofHom φ)) (gen (Ow w) E) (Spec.map (CommRingCat.ofHom τK))
      (gen (CrystallineSemistableComparison.OK l K.1) K.1) c₀ rfl eZ.hom eW.hom hZ1 hZ2 hW1 hW2
  · have hcp := compPart C.p (gen (Ow w) E) (Spec.map (CommRingCat.ofHom τK)) (D.s g) (D.t g) (D.comm g)
      c₀ (σ₀ i) (hσ i) (hu i) (hσ₁ i) ht'
    have hsq := square (Spec.map (CommRingCat.ofHom φ)) (gen (Ow w) E) (Spec.map (CommRingCat.ofHom τK))
      (gen (CrystallineSemistableComparison.OK l K.1) K.1) (σ₀ i ≫ D.t g) (hu i) eZ.hom eW.hom hZ1 hZ2 hW1 hW2
    exact hsq.trans (congrArg (eW.hom ≫ ·) hcp)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLowHodge
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
universe u v

private theorem isTr_transport {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {Z Y : Scheme.{0}} {p : Z ⟶ B}
    {q q' : Y ⟶ B} (e : q = q') {s : Y ⟶ Z} {tr : T.H q →ₗ[R] T.H p} (h : T.IsTr p q s tr) :
    ∃ tr' : T.H q' →ₗ[R] T.H p, T.IsTr p q' s tr' ∧
      ∀ {X : Scheme.{0}} {r : X ⟶ B} (t : Y ⟶ X) (h₁ : t ≫ r = q) (h₂ : t ≫ r = q') (y : T.H r),
        tr' (T.pull t h₂ y) = tr (T.pull t h₁ y) := by
  subst e
  exact ⟨tr, h, fun _ _ _ _ => rfl⟩

private theorem low_square {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : GlobalTheory.GalV.HTower k}
    {θ : H.Γ → L} {C : Cover H θ O} (D : LowData C) (g : H.Γ) :
    IsPullback (pullback.fst (D.s g ≫ C.p) (gen O k)) ((low D).s g) (D.s g) (pullback.fst C.p (gen O k)) := by
  have hls : (low D).s g ≫ pullback.snd C.p (gen O k) = pullback.snd (D.s g ≫ C.p) (gen O k) :=
    bcMap_snd (gen O k) (D.s g) rfl
  have hlf : (low D).s g ≫ pullback.fst C.p (gen O k) = pullback.fst (D.s g ≫ C.p) (gen O k) ≫ D.s g :=
    bcMap_fst (gen O k) (D.s g) rfl
  refine IsPullback.of_bot ?_ hlf.symm (IsPullback.of_hasPullback C.p (gen O k))
  convert IsPullback.of_hasPullback (D.s g ≫ C.p) (gen O k) using 2
  exact hls

theorem UpperTheory.Gal.G3.jLowHodge :
    HodgeGood → BcGood.{0} → FEtBasic → HodgeOpBc → CoverInv.{0} → LiesOp.{0} → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowHodge := by
  intro hHG hBG hFB hOB hCI hLO k L F _ _ _ _ φ ψ H θ O _ _ C D hN hO a hH
  unfold HOcc at hH ⊢
  unfold Nice at hN
  obtain ⟨b, x, hx, he⟩ := hH
  unfold IsHEig at he
  set T' := (hodge F a b).bc (Spec.map (CommRingCat.ofHom φ)) with hT'
  have hgood : T'.Good := hBG _ _ (hHG F a b)
  obtain ⟨hinj, hsurj⟩ := hCI C hO T' hgood
  have hH' : ∀ g : H.Γ, ∃ trg : T'.H (H.s g ≫ H.q) →ₗ[F] T'.H H.q,
      T'.IsTr H.q (H.s g ≫ H.q) (H.s g) trg ∧ trg (T'.pull (H.t g) (H.comm g) x) = ψ (θ g) • x := by
    intro g
    obtain ⟨d, hd⟩ := hN.2.2 g
    haveI : IsFinite (H.s g) := hd.1
    haveI : Etale (H.s g) := hd.2.1
    obtain ⟨i1, i2, tr, htr, heq⟩ := hOB k F φ H g a b
    obtain ⟨j1, j2, hg⟩ := he g
    exact ⟨tr, htr, (heq j1 j2 x).symm.trans hg⟩
  obtain ⟨z, hz⟩ := hsurj x (fun g _ hθ => by
    obtain ⟨trg, htr, heq⟩ := hH' g
    exact ⟨trg, htr, by rw [heq, hθ, map_one, one_smul]⟩)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hx (by rw [← hz]; exact map_zero _)
  refine ⟨b, z, hz0, ?_⟩
  unfold IsHEig
  intro g
  have hfet : FEt ((low D).s g) (D.d g) := hFB.1 _ _ _ _ _ (low_square D g) (D.fet g)
  haveI : IsFinite ((low D).s g) := hfet.1
  haveI : Etale ((low D).s g) := hfet.2.1
  obtain ⟨i1, i2, trL, htrL, heqL⟩ := hOB k F φ (low D) g a b
  refine ⟨i1, i2, ?_⟩
  rw [heqL i1 i2 z]
  obtain ⟨tr', htr', htrans⟩ := isTr_transport T' (q := (low D).s g ≫ (low D).q)
    (q' := pullback.snd (D.s g ≫ C.p) (gen O k)) (bcMap_snd (gen O k) (D.s g) rfl) htrL
  obtain ⟨trg, htrg, hgeq⟩ := hH' g
  have hlies := hLO C g (D.s g) (D.t g) (D.comm g) (D.m g) (D.d g) (D.lies g) hfet T' hgood tr' trg htr' htrg z
  rw [hz, hgeq, ← hz, ← map_smul] at hlies
  have h := hinj ((map_smul (T'.pull (piK C) _) (ψ (θ g)) z).trans hlies)
  have h₂ : bcMap (gen O k) (D.t g) (D.comm g) ≫ (low D).q = pullback.snd (D.s g ≫ C.p) (gen O k) :=
    ((low D).comm g).trans (bcMap_snd (gen O k) (D.s g) rfl)
  have h3 : tr' (T'.pull (bcMap (gen O k) (D.t g) (D.comm g)) h₂ z) =
      trL (T'.pull ((low D).t g) ((low D).comm g) z) := htrans ((low D).t g) ((low D).comm g) h₂ z
  have h' : ψ (θ g) • z = ((D.m g : ℕ) : F) • trL (T'.pull ((low D).t g) ((low D).comm g) z) :=
    h.trans (congrArg (fun w => ((D.m g : ℕ) : F) • w) h3)
  have hm : ((D.m g : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (D.lies g).1.ne'
  have hw : trL (T'.pull ((low D).t g) ((low D).comm g) z) = ψ (θ g / (D.m g : L)) • z := by
    rw [map_div₀, map_natCast, div_eq_inv_mul, mul_smul, h']
    exact (inv_smul_smul₀ hm _).symm
  exact hw
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLowNice
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem sq_bc {T Y S B : Scheme.{0}} (s : T ⟶ Y) (p : Y ⟶ S) (c : B ⟶ S) :
    IsPullback (pullback.fst (s ≫ p) c)
      (pullback.lift (pullback.fst (s ≫ p) c ≫ s) (pullback.snd (s ≫ p) c)
        (by rw [Category.assoc, pullback.condition]) : pullback (s ≫ p) c ⟶ pullback p c)
      s (pullback.fst p c) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd p c) (v₂₂ := p) (h₃₁ := c) ?_ ?_
    (IsPullback.of_hasPullback p c)
  · rw [pullback.lift_snd]
    exact IsPullback.of_hasPullback (s ≫ p) c
  · rw [pullback.lift_fst]

theorem UpperTheory.Gal.G3.jLowNice :
    FEtBasic → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowNice := by
  intro hb k L _ _ H θ O _ _ C D
  haveI : Smooth C.p := C.smooth
  refine ⟨?_, ?_, ?_⟩
  · show Smooth (pullback.snd C.p (UpperTheory.Gal.Int.Geo.gen O k))
    infer_instance
  · exact GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap O k) C.proj
  · intro g
    exact ⟨D.d g, hb.1 _ _ _ _ _ (sq_bc (D.s g) C.p (UpperTheory.Gal.Int.Geo.gen O k)) (D.fet g)⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JModBc
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jModBc :
    UpperTheory.Gal.Seam.GoodOf → ModBc := by
  intro hG l _ K O _ _ φ Y W p d hs hp c _ _
  haveI : SmoothOfRelativeDimension d p := hs
  haveI : SmoothOfRelativeDimension 0 c := (Etale.iff_smoothOfRelativeDimension_zero c).1 inferInstance
  have hcs : SmoothOfRelativeDimension d (c ≫ p) := by
    have h : SmoothOfRelativeDimension (0 + d) (c ≫ p) := inferInstance
    rwa [Nat.zero_add] at h
  have hqs : SmoothOfRelativeDimension d (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hcs
  have hcq : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (c ≫ p) :=
    GlobalTheory.isQProjOver_comp_of_isFinite_general c (GlobalTheory.SchemeWords.isQProjOver_of_isProjOver hp)
  haveI : IsProper p := GlobalTheory.SchemeWords.isProper_of_isProjOver hp
  have hcp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (c ≫ p) :=
    GlobalTheory.UPel.isProjOver_of_isQProjOver_of_isProper O W (c ≫ p) hcq inferInstance
  have hqp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    GlobalTheory.ProjSpace.isProjOver_pullback_snd φ hcp
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  have hsm : Smooth (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    SmoothOfRelativeDimension.smooth d _
  exact ⟨⟨hG l K.1 ⟨_, _⟩ hsm hqp, hsm⟩, hqs⟩
end

