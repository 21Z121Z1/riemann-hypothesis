import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmBilin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0019
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0013
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeformCr
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.DeformationPairing

private def extRep {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) :
    Representation A G (V × A) where
  toFun g := ((ρ g).comp (LinearMap.fst A V A) + (LinearMap.snd A V A).smulRight (c g)).prod (LinearMap.snd A V A)
  map_one' := by
    have h1 : c 1 = 0 := by simpa using hc 1 1
    refine LinearMap.ext fun x => ?_
    simp [h1]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    simp [hc, add_assoc, add_comm, add_left_comm]

private theorem extRep_apply {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (g : G) (x : V × A) :
    extRep ρ c hc g x = (ρ g x.1 + x.2 • c g, x.2) := rfl

private theorem contAction_sub {G A V : Type} [Group G] [TopologicalSpace G] [CommRing A] [AddCommGroup V]
    [Module A V] [TopologicalSpace V] (ρ : Representation A G V) (h : ContAction ρ) (H : Subgroup G) :
    ContAction (ρ.comp H.subtype : Representation A H V) :=
  h.comp (f := fun p : H × V => ((p.1 : G), p.2))
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

private noncomputable def pair (Q : Type) {E : Type} [Field Q] [Field E] [Algebra Q E] (n : ℕ) :
    (Matrix (Fin n) (Fin n) E × E) →ₗ[Q] (Fin n → E) →ₗ[Q] (Fin n → DualNumber E) :=
  LinearMap.mk₂ Q (fun w v i => (⟨w.2 * v i, (w.1.mulVec v) i⟩ : DualNumber E))
    (fun w w' v => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [add_mul, Matrix.add_mulVec] <;> rfl)
    (fun c w v => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [Matrix.smul_mulVec] <;> rfl)
    (fun w v v' => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [mul_add, Matrix.mulVec_add] <;> rfl)
    (fun c w v => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [Matrix.mulVec_smul] <;> rfl)

private theorem pair_fst (Q : Type) {E : Type} [Field Q] [Field E] [Algebra Q E] (n : ℕ)
    (w : Matrix (Fin n) (Fin n) E × E) (v : Fin n → E) (i : Fin n) : (pair Q n w v i).fst = w.2 * v i := rfl

private theorem pair_snd (Q : Type) {E : Type} [Field Q] [Field E] [Algebra Q E] (n : ℕ)
    (w : Matrix (Fin n) (Fin n) E × E) (v : Fin n → E) (i : Fin n) :
    (pair Q n w v i).snd = (w.1.mulVec v) i := rfl

private theorem mulVec_fst {E : Type} [Field E] {n : ℕ} (R S : Matrix (Fin n) (Fin n) E)
    (R' : Matrix (Fin n) (Fin n) (DualNumber E)) (h : ∀ i j, R' i j = ⟨R i j, S i j⟩)
    (w : Fin n → DualNumber E) (i : Fin n) :
    (R'.mulVec w i).fst = R.mulVec (fun j => (w j).fst) i := by
  have h1 : ∀ i j, (R' i j).fst = R i j := fun i j => by rw [h]; rfl
  simp [Matrix.mulVec, dotProduct, TrivSqZeroExt.fst_sum, h1]

private theorem mulVec_snd {E : Type} [Field E] {n : ℕ} (R S : Matrix (Fin n) (Fin n) E)
    (R' : Matrix (Fin n) (Fin n) (DualNumber E)) (h : ∀ i j, R' i j = ⟨R i j, S i j⟩)
    (w : Fin n → DualNumber E) (i : Fin n) :
    (R'.mulVec w i).snd = R.mulVec (fun j => (w j).snd) i + S.mulVec (fun j => (w j).fst) i := by
  have h1 : ∀ i j, (R' i j).fst = R i j := fun i j => by rw [h]; rfl
  have h2 : ∀ i j, (R' i j).snd = S i j := fun i j => by rw [h]; rfl
  simp [Matrix.mulVec, dotProduct, TrivSqZeroExt.snd_sum, h1, h2, Finset.sum_add_distrib]

private theorem ad_mulVec {G E : Type} [Group G] [Field E] {n : ℕ} (r : G →* GL (Fin n) E) (g : G)
    (X : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    (adGL r g X).mulVec (colRep r g v) = colRep r g (X.mulVec v) := by
  change ((r g : Matrix (Fin n) (Fin n) E) * X * ((r g)⁻¹ : GL (Fin n) E)).mulVec
    (Matrix.toLin' (r g : Matrix (Fin n) (Fin n) E) v) = Matrix.toLin' (r g : Matrix (Fin n) (Fin n) E) _
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

end UpperTheory.V.Loc.DeformationPairing

open UpperTheory.V.Loc.DeformationPairing in
theorem UpperTheory.V.Loc.deformCr :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] {n : ℕ} (r : G →* GL (Fin n) E), Continuous (fun g => (r g : Matrix (Fin n) (Fin n) E)) → ∀ y ∈ Z1 (adGL r), ∀ r' : G →* GL (Fin n) (DualNumber E), (∀ g i j, (r' g : Matrix (Fin n) (Fin n) (DualNumber E)) i j = ⟨(r g : Matrix (Fin n) (Fin n) E) i j, (y g * (r g : Matrix (Fin n) (Fin n) E)) i j⟩) → ∀ (H : Subgroup G) [H.Normal], IsOpen (H : Set G) → (CrOn φ (colRep r') H ↔ CrOn φ (colRep r) H ∧ y ∈ UpperTheory.V.Loc.finiteCocycles φ (adGL r)) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ _ n r hr y hy r' hr' H _ hH
  haveI : IsModuleTopology ℚ_[l] (DualNumber E) := inferInstanceAs (IsModuleTopology ℚ_[l] (E × E))
  haveI : FiniteDimensional ℚ_[l] (DualNumber E) := inferInstanceAs (FiniteDimensional ℚ_[l] (E × E))
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin n → Fin n → E))
  have hψ : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  have cV : ContAction (colRep r) :=
    Continuous.matrix_mulVec (hr.comp continuous_fst) continuous_snd
  have hr'c : Continuous (fun g => (r' g : Matrix (Fin n) (Fin n) (DualNumber E))) := by
    refine continuous_matrix fun i j => ?_
    simp only [hr']
    exact (hr.matrix_elem i j).prodMk ((hy.1.matrix_mul hr).matrix_elem i j)
  have cW : ContAction (colRep r') :=
    Continuous.matrix_mulVec (hr'c.comp continuous_fst) continuous_snd
  have cM : ContAction (adGL r) := by
    have hi : Continuous (fun g => (((r g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) := by
      simp only [← map_inv]
      exact hr.comp continuous_inv
    exact ((hr.comp continuous_fst).matrix_mul continuous_snd).matrix_mul (hi.comp continuous_fst)
  have cH : ContAction (extRep (adGL r) y hy.2) := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [extRep_apply]
    refine Continuous.prodMk (Continuous.add ?_ ?_) (continuous_snd.comp continuous_snd)
    · exact Continuous.comp (f := fun p : G × (Matrix (Fin n) (Fin n) E × E) => (p.1, p.2.1)) cM (by fun_prop)
    · exact (continuous_snd.comp continuous_snd).smul (hy.1.comp continuous_fst)
  have hb : ∀ g w v, pair ℚ_[l] n (extRep (adGL r) y hy.2 g w) (colRep r g v)
      = colRep r' g (pair ℚ_[l] n w v) := by
    intro g w v
    funext i
    have e' : colRep r' g (pair ℚ_[l] n w v)
      = (r' g : Matrix (Fin n) (Fin n) (DualNumber E)).mulVec (pair ℚ_[l] n w v) := rfl
    have e : ∀ u, colRep r g u = (r g : Matrix (Fin n) (Fin n) E).mulVec u := fun _ => rfl
    have e1 : (fun j => (pair ℚ_[l] n w v j).fst) = w.2 • v := rfl
    have e2 : (fun j => (pair ℚ_[l] n w v j).snd) = w.1.mulVec v := rfl
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [e', mulVec_fst _ _ _ (hr' g), e1, pair_fst, extRep_apply, Matrix.mulVec_smul, e]; rfl
    · rw [e', mulVec_snd _ _ _ (hr' g), e1, e2, pair_snd, extRep_apply, Matrix.add_mulVec, ad_mulVec, e, e,
        Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      rfl
  have crM : CrOn φ (colRep r) H → CrOn φ (adGL r) H := fun h =>
    (isCrys_isDR_internalHom (φ.comp H.subtype) hψ _ _ _ (contAction_sub _ cV H) (contAction_sub _ cV H) (contAction_sub _ cM H)
      (LinearMap.mk₂ ℚ_[l] (fun (X : Matrix (Fin n) (Fin n) E) (v : Fin n → E) => X.mulVec v)
        (fun _ _ _ => Matrix.add_mulVec _ _ _) (fun _ _ _ => Matrix.smul_mulVec _ _ _)
        (fun _ _ _ => Matrix.mulVec_add _ _ _) (fun _ _ _ => Matrix.mulVec_smul _ _ _))
      (fun g X v => ad_mulVec r g X v)
      (fun X Y hXY => Matrix.ext_iff_mulVec.2 fun v => LinearMap.congr_fun hXY v)).1 h h
  have cr1 : CrOn φ (chRep (1 : G →* Eˣ)) H :=
    crUnr (A := ℚ_[l]) (φ.comp H.subtype) hψ
      (resCoef ℚ_[l] ((chRep (1 : G →* Eˣ)).comp H.subtype : Representation E H E))
      (by
        unfold ReciprocityTheory.Gal.ContAction
        simpa [resCoef, chRep] using continuous_snd) 0
      (fun g _ x => by simp [resCoef, chRep])
  have htw : twist (1 : G →* Eˣ)⁻¹ (adGL r) = adGL r := by
    refine MonoidHom.ext fun g => ?_
    simp [twist]
  have key : CrOn φ (colRep r) H →
      (CrOn φ (extRep (adGL r) y hy.2) H ↔ y ∈ UpperTheory.V.Loc.finiteCocycles φ (adGL r)) := fun h => by
    have := crExt φ hφ (adGL r) (extRep (adGL r) y hy.2) cM cH 1 (LinearMap.inl E _ E) (LinearMap.snd E _ E)
      (0, 1) y LinearMap.inl_injective (Function.Exact.inl_snd) rfl
      (fun g x => by simp [extRep_apply]) (fun g => by simp [extRep_apply]) H hH (crM h) cr1
    rwa [htw] at this
  constructor
  · intro hW
    have hV : CrOn φ (colRep r) H := by
      refine ((isCrys_isDR_sub_quot (φ.comp H.subtype) hψ _ _ (contAction_sub _ cW H) (contAction_sub _ cV H)
        (((TrivSqZeroExt.fstHom ℚ_[l] E E).toLinearMap).compLeft (Fin n)) (fun g x => ?_)).2 (fun v => ?_)).1 hW
      · funext i
        exact mulVec_fst _ _ _ (hr' g) x i
      · exact ⟨fun i => TrivSqZeroExt.inl (v i), rfl⟩
    refine ⟨hV, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : y = 0 := Subsingleton.elim _ _
      rw [this]; exact Submodule.zero_mem _
    · refine (key hV).1 ?_
      refine (isCrys_isDR_internalHom (A := ℚ_[l]) (φ.comp H.subtype) hψ
        (resCoef ℚ_[l] ((colRep r).comp H.subtype : Representation E H _))
        (resCoef ℚ_[l] ((colRep r').comp H.subtype : Representation (DualNumber E) H _))
        (resCoef ℚ_[l] ((extRep (adGL r) y hy.2).comp H.subtype : Representation E H _))
        (contAction_sub _ cV H) (contAction_sub _ cW H) (contAction_sub _ cH H) (pair ℚ_[l] n)
        (fun g w v => hb g w v) (fun w w' h => ?_)).1 hV hW
      refine Prod.ext (Matrix.ext_iff_mulVec.2 fun v => funext fun i => ?_) ?_
      · rw [← pair_snd ℚ_[l], ← pair_snd ℚ_[l], h]
      · have := pair_fst ℚ_[l] n w 1 ⟨0, hn⟩
        rw [h, pair_fst] at this
        simpa using this.symm
  · rintro ⟨hV, hy'⟩
    refine (admissible_of_bilinear_openSubgroup_galois (A := ℚ_[l]) (φ.comp H.subtype) hψ
        (resCoef ℚ_[l] ((extRep (adGL r) y hy.2).comp H.subtype : Representation E H _))
        (resCoef ℚ_[l] ((colRep r).comp H.subtype : Representation E H _))
        (resCoef ℚ_[l] ((colRep r').comp H.subtype : Representation (DualNumber E) H _))
        (contAction_sub _ cH H) (contAction_sub _ cV H) (contAction_sub _ cW H) (pair ℚ_[l] n)
        (fun g w v => hb g w v) ?_).1 ((key hV).2 hy') hV
    refine eq_top_iff.2 fun x _ => ?_
    have : x = pair ℚ_[l] n (0, 1) (fun i => (x i).fst) + pair ℚ_[l] n (1, 0) (fun i => (x i).snd) := by
      funext i
      refine TrivSqZeroExt.ext ?_ ?_ <;> simp [pair_fst, pair_snd]
    rw [this]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨(_, _), rfl⟩) (Submodule.subset_span ⟨(_, _), rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineExtensionIffMemFiniteCocycles
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (a b : G →* Bˣ), Continuous (fun g => (a g : B)) → Continuous (fun g => (b g : B)) → ∀ (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((a / b) g : Bˣ) * x h), Continuous x → IsCr φ (chRep a) → IsCr φ (chRep b) → (IsCr φ (ext2 a b x hx) ↔ x ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (a / b))) := by
  intro l _ G _ _ _ φ hφ B _ _ _ _ _ _ a b ha hb x hx hc h1 h2
  have key := UpperTheory.V.Loc.crExt φ hφ (chRep a) (ext2 a b x hx) (contAction_chRep ha) (contAction_charExtension_of_continuous_cocycle ha hb hx hc)
    b (LinearMap.inl B B B) (LinearMap.snd B B B) (0, 1) x LinearMap.inl_injective Function.Exact.inl_snd rfl
    (fun g v => by simp [characterExtensionRep_apply, chRep_apply]) (fun g => by simp [characterExtensionRep_apply, mul_comm])
    ⊤ (by simp) ((crOn_top φ _).2 h1) ((crOn_top φ _).2 h2)
  have e : twist b⁻¹ (chRep a) = chRep (a / b) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [twist_apply, chRep_apply, chRep_apply, div_eq_mul_inv, MonoidHom.mul_apply, Units.val_mul, smul_eq_mul]
    ring
  rwa [crOn_top, e] at key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineUpperTriangularIffMemFiniteCocycles
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (κ : Fin 3 → G →* Bˣ), (∀ i, Continuous fun g => (κ i g : B)) → ∀ (x y z : G → B) (ρ : G →* GL (Fin 3) B), Continuous x → Continuous y → Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) → ∀ hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h, IsCr φ (ext2 (κ 0) (κ 1) x hx) → IsCr φ (chRep (κ 2)) → (IsCr φ (colRep ρ) ↔ (fun g => (z g, y g)) ∈ UpperTheory.V.Loc.finiteCocycles φ (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx))) := by
  intro l _ G _ _ _ φ hφ B _ _ _ _ _ _ κ hκ x y z ρ cx cy cz hρ hx h1 h2
  have hc : Continuous fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) := by
    simp only [hρ]
    exact continuous_triM (t := fun g i => κ i g) hκ cx cy cz
  let f : (B × B) →ₗ[B] (Fin 3 → B) :=
    { toFun := fun v => ![v.1, v.2, 0]
      map_add' := fun v w => by ext i; fin_cases i <;> simp
      map_smul' := fun c v => by ext i; fin_cases i <;> simp }
  have hf : ∀ v, f v = ![v.1, v.2, 0] := fun _ => rfl
  rw [← crOn_top]
  refine crExt φ hφ (ext2 (κ 0) (κ 1) x hx) (colRep ρ) (contAction_charExtension_of_continuous_cocycle (hκ 0) (hκ 1) hx cx)
    (contAction_colRep hc) (κ 2) f (LinearMap.proj 2) ![0, 0, 1] (fun g => (z g, y g)) ?_ ?_ ?_ ?_ ?_ ⊤
    (by simp) ((crOn_top _ _).2 h1) ((crOn_top _ _).2 h2)
  · intro v w h
    exact Prod.ext (congrFun h 0) (congrFun h 1)
  · intro v
    constructor
    · intro h
      refine ⟨(v 0, v 1), ?_⟩
      have h' : v 2 = 0 := h
      ext i
      fin_cases i <;> simp [hf, h']
    · rintro ⟨w, rfl⟩
      rfl
  · rfl
  · intro g v
    rw [colRep_apply, hρ, characterExtensionRep_apply]
    ext i
    fin_cases i <;> simp [hf, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · intro g
    rw [colRep_apply, hρ]
    ext i
    fin_cases i <;> simp [hf, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemGKBot
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.R0

variable {l : ℕ} [Fact l.Prime]

theorem mem_Dcr {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (ρ : Representation A G V) (x : V ⊗[ℚ_[l]] Bcr l) :
    x ∈ Dcr φ ρ ↔ ∀ g, actC φ ρ g x = x := by
  simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_Ddr {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (ρ : Representation A G V) (x : V ⊗[ℚ_[l]] Bdr l) :
    x ∈ Ddr φ ρ ↔ ∀ g, actD φ ρ g x = x := by
  simp only [Ddr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_GK_bot (g : GQ l) : g ∈ GK (botExt l) := by simp [GK, botExt]

variable {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [TopologicalSpace E]
  [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]

theorem char_cr (κ : GQ l →* Eˣ) (h : IsCr (GK (botExt l)).subtype (chRep (κ.comp (GK (botExt l)).subtype))) :
    ∃ x : E ⊗[ℚ_[l]] Bcr l, (∀ g, actC (MonoidHom.id _) (chRep κ) g x = x) ∧ ∀ (L : FinExt l),
      ∀ y ∈ Dcr (GK L).subtype (chRep (κ.comp (GK L).subtype)), ∃! c : E ⊗[ℚ_[l]] ↥(K0 L), y = smulC E L c x := by
  obtain ⟨T⟩ := tiedP l
  have hdom : IsDomain (PP l).R.B := GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)
  have hc := (isCrField (botExt l) _).1.1 ((isCrIff (botExt l) _).1.1 h)
  have hf : GlobalTheory.RegularRing.FracInv ((PP l).PD (botExt l)) := by
    intro x y hx h
    refine GlobalTheory.Per.FracInv.tied_frac_invariant l _ _ T _ y x hx fun g hg => ?_
    have h1 := h ⟨g, hg⟩
    rw [(PP l).PD_actB, (PP l).PD_actB] at h1
    rw [mul_comm, h1, mul_comm]
  have hu : GlobalTheory.RegularRing.LineUnit ((PP l).PD (botExt l)) := by
    intro b hb h
    refine (GlobalTheory.T.periodRings_regular_phi_surjective_fil l _ _ T).1 (botExt l) b hb fun g hg => ?_
    obtain ⟨x, hx⟩ := h ⟨g, hg⟩
    exact ⟨x, by rw [← (PP l).PD_actB (botExt l) ⟨g, hg⟩, hx, Algebra.smul_def]⟩
  obtain ⟨m, b, d, hd, h1⟩ := GlobalTheory.Per.TiedSpan.exists_sum_of_isCrys _ hf hu _ hc 1
  have h0 : finrank ℚ_[l] ↥(K0 (botExt l)) = 1 := by
    rw [show K0 (botExt l) = ⊥ from bot_inf_eq _, IntermediateField.finrank_bot]
  rw [IsCrys, h0, finrank_self] at hc
  obtain ⟨x, hx, hxu⟩ := unit_of_span _ hc b d hd h1
  have hx' : ∀ g, actC (MonoidHom.id _) (chRep κ) g x = x := by
    intro g
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hx
    refine Eq.trans ?_ (hx ⟨g, mem_GK_bot g⟩)
    unfold actC actVB
    congr 2
    ext b
    exact ((PP l).PD_actB (botExt l) ⟨g, mem_GK_bot g⟩ b).symm
  refine ⟨x, hx', fun L y hy => ?_⟩
  exact basis_of_unit (H := ↥(GK L)) (fun g => (PP l).actQ g)
    (fun b hb => ((PP l).PD L).invB b fun g => by rw [(PP l).PD_actB]; exact hb g) (fun g => (κ g : E))
    (actC (GK L).subtype (chRep (κ.comp (GK L).subtype))) (fun g v b => rfl) (smulC E L) (fun e f v b => rfl)
    x hxu (fun g => hx' g) y ((mem_Dcr _ _ _).1 hy)

theorem char_dr (κ : GQ l →* Eˣ) (h : IsDr (GK (botExt l)).subtype (chRep (κ.comp (GK (botExt l)).subtype))) :
    ∃ x : E ⊗[ℚ_[l]] Bdr l, (∀ g, actD (MonoidHom.id _) (chRep κ) g x = x) ∧ ∀ (L : FinExt l),
      ∀ y ∈ Ddr (GK L).subtype (chRep (κ.comp (GK L).subtype)), ∃! c : E ⊗[ℚ_[l]] ↥L.1, y = smulD E L c x := by
  obtain ⟨T⟩ := tiedP l
  have hF := GlobalTheory.RegularRing.isField_of_tied T
  have := hF.nontrivial
  have hc := (isCrField (botExt l) _).2.1.1 ((isCrIff (botExt l) _).2.1 h)
  obtain ⟨m, b, d, hd, h1⟩ := GlobalTheory.Per.DeRhamSpan.span_of_isField _ _ hF hc 1
  have h0 : finrank ℚ_[l] ↥(botExt l).1 = 1 := IntermediateField.finrank_bot
  rw [IsDR, h0, finrank_self] at hc
  obtain ⟨x, hx, hxu⟩ := unit_of_span _ hc b d hd h1
  have hx' : ∀ g, actD (MonoidHom.id _) (chRep κ) g x = x := by
    intro g
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hx
    refine Eq.trans ?_ (hx ⟨g, mem_GK_bot g⟩)
    unfold actD actVdR
    congr 2
    ext b
    exact ((PP l).PD_actdR (botExt l) ⟨g, mem_GK_bot g⟩ b).symm
  refine ⟨x, hx', fun L y hy => ?_⟩
  exact basis_of_unit (H := ↥(GK L)) (fun g => (PP l).actQdR g)
    (fun b hb => ((PP l).PD L).invdR b fun g => by rw [(PP l).PD_actdR]; exact hb g) (fun g => (κ g : E))
    (actD (GK L).subtype (chRep (κ.comp (GK L).subtype))) (fun g v b => rfl) (smulD E L) (fun e f v b => rfl)
    x hxu (fun g => hx' g) y ((mem_Ddr _ _ _).1 hy)

end UpperTheory.V.Loc.R0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NormLeOneOfMemSpectrumFrobeniusMatrixFilZero
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private noncomputable def filS {l : ℕ} [Fact l.Prime] (K : FinExt l) : Subring (Bcr l) where
  carrier := {x | ∀ k : ℕ, (PP l).ιB (((PP l).φB ^ k) x) ∈ ((PP l).PD K).Fil 0}
  mul_mem' := fun {a b} ha hb k => by
    rw [map_mul, map_mul]
    simpa using ((PP l).PD K).Fil_mul 0 0 _ _ (ha k) (hb k)
  one_mem' := fun k => by
    rw [map_one, map_one]; exact ((PP l).PD K).one_mem
  add_mem' := fun {a b} ha hb k => by
    rw [map_add, map_add]; exact Submodule.add_mem _ (ha k) (hb k)
  zero_mem' := fun k => by
    rw [map_zero, map_zero]; exact Submodule.zero_mem _
  neg_mem' := fun {a} ha k => by
    rw [map_neg, map_neg]; exact Submodule.neg_mem _ (ha k)

private theorem frobenius_iterate_unramified {l : ℕ} [Fact l.Prime] (K : FinExt l) (k : ℕ) (c : ↥(K0 K)) :
    ((PP l).φB)^[k] (algebraMap ↥(K0 K) (Bcr l) c) =
      algebraMap ↥(K0 K) (Bcr l) ((((PP l).PD K).σ)^[k] c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, ← (PP l).PD_φ K,
      ((PP l).PD K).φ_K₀]

private theorem K0_mem {l : ℕ} [Fact l.Prime] (K : FinExt l) (c : ↥(K0 K)) :
    algebraMap ↥(K0 K) (Bcr l) c ∈ filS K := by
  intro k
  rw [AlgHom.coe_pow, frobenius_iterate_unramified, ← (PP l).PD_ι K, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    ← algebraMap_smul ↥K.1]
  exact Submodule.smul_mem _ _ ((PP l).PD K).one_mem

private theorem fil_iff {l : ℕ} [Fact l.Prime] (K K' : FinExt l) (x : Bdr l) :
    x ∈ ((PP l).PD K).Fil 0 ↔ x ∈ ((PP l).PD K').Fil 0 := by
  obtain ⟨T⟩ := tiedP l
  rw [T.fil, T.fil]

theorem UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ {d : ℕ} (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (F : Matrix (Fin d) (Fin d) ↥(K0 K)), M' * M = 1 → (∀ (k : ℕ) i j, (PP l).ιB (((PP l).φB)^[k] (M i j)) ∈ ((PP l).PD (botExt l)).Fil 0) → M.map (((PP l).φB)^[f]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ a ∈ spectrum (Om l) (F.map (algebraMap ↥(K0 K) (Om l))), ‖a‖ ≤ 1 := by
  intro l _ K f hf hσ d M M' F hM hFil hφ a ha
  obtain ⟨T⟩ := tiedP l
  haveI : IsDomain (Bcr l) := GlobalTheory.RegularRing.isDomain_of_tied T K
  obtain ⟨r, Y, Z, F', hr, hZY, hFY, hdet⟩ := UpperTheory.exists_invariant_block_det_norm_eq_pow_of_mem_spectrum (K0 K) F a ha
  set j : ↥(K0 K) →+* Bcr l := algebraMap ↥(K0 K) (Bcr l) with hj
  let ψ : Bcr l →+* Bcr l := (((PP l).φB ^ f : Bcr l →ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l)
  have hψ : (ψ : Bcr l → Bcr l) = ((PP l).φB)^[f] := AlgHom.coe_pow _ _
  obtain ⟨X, hXd⟩ : ∃ X : Matrix (Fin d) (Fin r) (Bcr l), X = M * Y.map j := ⟨_, rfl⟩
  have hZX : (Z.map j * M') * X = 1 := by
    rw [hXd]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M', hM, Matrix.one_mul, ← Matrix.map_mul, hZY,
      Matrix.map_one _ (map_zero j) (map_one j)]
  have hYψ : (Y.map j).map ψ = Y.map j := by
    ext i k
    simp only [Matrix.map_apply]
    rw [hψ, hj, frobenius_iterate_unramified, hσ]
  have hX : X.map ψ = X * F'.map j := by
    rw [hXd]
    rw [Matrix.map_mul, hYψ, hψ, hφ, Matrix.mul_assoc, ← Matrix.map_mul, hFY, Matrix.map_mul,
      Matrix.mul_assoc]
  obtain ⟨s, hs⟩ := UpperTheory.exists_square_submatrix_det_ne_zero_of_left_inverse X _ hZX
  have hXS : ∀ i k, X i k ∈ filS K := by
    intro i k
    simp only [hXd, Matrix.mul_apply, Matrix.map_apply]
    refine Subring.sum_mem _ fun c _ => Subring.mul_mem _ (fun n => ?_) (K0_mem K _)
    rw [AlgHom.coe_pow]
    exact (fil_iff _ _ _).1 (hFil n i c)
  have hbS : (X.submatrix s id).det ∈ filS K := by
    rw [Matrix.det_apply']
    exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (intCast_mem _ _)
      (Subring.prod_mem _ fun i _ => hXS _ _)
  have hb : ((PP l).φB)^[f] (X.submatrix s id).det = j F'.det * (X.submatrix s id).det := by
    have h1 : (X.submatrix s id).map ψ = X.submatrix s id * F'.map j := by
      ext i k
      have := congrFun (congrFun hX (s i)) k
      simpa [Matrix.mul_apply] using this
    rw [← hψ, RingHom.map_det, RingHom.mapMatrix_apply, h1, Matrix.det_mul, mul_comm,
      RingHom.map_det, RingHom.mapMatrix_apply]
  have hle := UpperTheory.norm_le_one_of_frobenius_pow_eigenvector_mem_fil_zero K f hf hσ _ F'.det hs hb fun i => by
    have := hbS i
    rw [AlgHom.coe_pow] at this
    exact (fil_iff _ _ _).1 this
  rw [hdet] at hle
  exact (pow_le_one_iff_of_nonneg (norm_nonneg a) hr.ne').1 hle
end

