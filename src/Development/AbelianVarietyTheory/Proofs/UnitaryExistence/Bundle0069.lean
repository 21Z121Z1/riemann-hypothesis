import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0066
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0010
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0037
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjugationActsOnCmTorsionByMultiplication
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.Acts

theorem corr (ω : ℂ) (f : ℤ × ℤ → ℂ) (hf : ∀ s, f s = s.1 + s.2 * ω) (R : ℂ → ℂ → Prop)
    (tot : ∀ z, ∃ z', R z z') (sur : ∀ z', ∃ z, R z z')
    (add : ∀ z z' y y', R z z' → R y y' → R (z + y) (z' + y'))
    (om : ∀ z z', R z z' → R (ω * z) (ω * z'))
    (iff : ∀ z z' y y', R z z' → R y y' → ((∃ a, z - y = f a) ↔ ∃ a, z' - y' = f a))
    (rsp : ∀ z z' y', R z z' → (∃ a, z' - y' = f a) → R z y') (n : ℕ) (hn : 0 < n) :
    (∃ s, ∀ a, R (f a / n) (f s * f a / n)) ∧
      ∀ s, (∀ a, R (f a / n) (f s * f a / n)) → ∃ s' a, f s' * f s = 1 + n * f a := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have f0 : f (0, 0) = 0 := by simp [hf]
  have f1 : f (1, 0) = 1 := by simp [hf]
  have h0 : R 0 0 := by
    obtain ⟨z', h⟩ := tot 0
    obtain ⟨a, ha⟩ := (iff _ _ _ _ (add _ _ _ _ h h) h).1 ⟨(0, 0), by simp [f0]⟩
    exact rsp _ _ _ h ⟨a, by rw [← ha]; ring⟩
  have neg : ∀ z z', R z z' → R (-z) (-z') := by
    intro z z' h
    obtain ⟨y, hy⟩ := tot (-z)
    obtain ⟨a, ha⟩ := (iff _ _ _ _ (add _ _ _ _ h hy) h0).1 ⟨(0, 0), by simp [f0]⟩
    exact rsp _ _ _ hy ⟨a, by rw [← ha]; ring⟩
  have int : ∀ (m : ℤ) z z', R z z' → R (m * z) (m * z') := by
    intro m z z' h
    induction m using Int.induction_on with
    | zero => simpa using h0
    | succ k ih =>
      have := add _ _ _ _ ih h
      convert this using 1 <;> push_cast <;> ring
    | pred k ih =>
      have := add _ _ _ _ ih (neg _ _ h)
      convert this using 1 <;> push_cast <;> ring
  have mul : ∀ a z z', R z z' → R (f a * z) (f a * z') := by
    intro a z z' h
    have := add _ _ _ _ (int a.1 _ _ h) (int a.2 _ _ (om _ _ h))
    convert this using 1 <;> rw [hf] <;> ring
  constructor
  · obtain ⟨z', h⟩ := tot (1 / n)
    obtain ⟨s, hs⟩ := (iff _ _ _ _ (int n _ _ h) h0).1 ⟨(1, 0), by rw [f1]; push_cast; field_simp; ring⟩
    refine ⟨s, fun a => ?_⟩
    have := mul a _ _ h
    convert this using 1
    · ring
    · rw [← hs]; push_cast; field_simp; ring
  · intro s hs
    obtain ⟨z, h⟩ := sur (1 / n)
    obtain ⟨s', hs'⟩ := (iff _ _ _ _ (int n _ _ h) h0).2 ⟨(1, 0), by rw [f1]; push_cast; field_simp; ring⟩
    obtain ⟨a, ha⟩ := (iff _ _ _ _ (hs s') h).1 ⟨(0, 0), by rw [f0, ← hs']; push_cast; field_simp; ring⟩
    refine ⟨s', a, ?_⟩
    rw [← ha]; field_simp; ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_symm (τ : ℂ ≃+* ℂ) : spMap (τ.symm : ℂ →+* ℂ) ≫ spMap (τ : ℂ →+* ℂ) = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x; simp

theorem pt_over (C : Curve H) (z : ℂ) : C.pt z ≫ C.P.A.hom = 𝟙 _ := Over.w (C.u.ex fun _ => C.c * z)

theorem pt_add (C : Curve H) {f : Sp ℂ ⟶ Sp ℂ} {io : C.P.A.left ⟶ C.P.A.left}
    (h : IsGrpPullback C.P.A C.P.A f io) {z z' y y' : ℂ} (hz : C.pt z' ≫ io = f ≫ C.pt z)
    (hy : C.pt y' ≫ io = f ≫ C.pt y) : C.pt (z' + y') ≫ io = f ≫ C.pt (z + y) := by
  have e : ∀ a b, C.pt (a + b) = (C.u.ex (fun _ => C.c * a) * C.u.ex (fun _ => C.c * b)).left := by
    intro a b
    rw [← C.u.ex_add, Curve.pt]
    congr 2
    funext _; simp [mul_add]
  let U : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ f) ⟶ 𝟙_ (Over (Sp ℂ)) := Over.homMk f (by simp)
  have := h.2 _ (C.u.ex fun _ => C.c * z') (C.u.ex fun _ => C.c * y') (U ≫ C.u.ex fun _ => C.c * z)
    (U ≫ C.u.ex fun _ => C.c * y) hz.symm hy.symm
  rw [← MonObj.comp_mul] at this
  rw [e, e]
  exact this.symm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ n : ℕ, 0 < n → (∃ s, C.ActsBy τ io n s) ∧ ∀ s, C.ActsBy τ io n s → (∃ s' a, wC H s' * wC H s = 1 + n * wC H a) ∧ ∀ m : ℕ, m ∣ n → C.ActsBy τ io m s := by
  intro E _ _ _ H C τ hτ io h n hn
  obtain ⟨W, -, hW, hker, hon, hcomm⟩ := GlobalTheory.T.exists_cmEndomorphism_comm_conjugation E H C
  have hc := hcomm τ hτ io h
  have key := corr (wC H (0, 1)) (wC H) (fun s => by simp [wC])
    (fun z z' => C.pt z' ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z)
    (fun z => by
      have w : (spMap (τ : ℂ →+* ℂ) ≫ C.pt z) ≫ C.P.A.hom = 𝟙 _ ≫ spMap (τ : ℂ →+* ℂ) := by
        rw [Category.assoc, pt_over]; simp
      obtain ⟨z', hz⟩ := hon (h.1.lift _ _ w) (h.1.lift_snd _ _ w)
      exact ⟨z', by rw [hz, h.1.lift_fst]⟩)
    (fun z' => by
      obtain ⟨z, hz⟩ := hon (spMap (τ.symm : ℂ →+* ℂ) ≫ C.pt z' ≫ io) (by
        rw [Category.assoc, Category.assoc, h.1.w, ← Category.assoc (C.pt z'), pt_over, Category.id_comp,
          spMap_symm])
      refine ⟨z, ?_⟩
      have := spMap_symm τ.symm
      rw [RingEquiv.symm_symm] at this
      rw [hz, ← Category.assoc, this, Category.id_comp])
    (fun z z' y y' hz hy => pt_add C h hz hy)
    (fun z z' hz => by
      rw [← hW, ← hW, Category.assoc, hc, ← Category.assoc, hz, Category.assoc])
    (fun z z' y y' hz hy => by
      rw [← hker, ← hker]
      constructor
      · intro e
        apply h.1.hom_ext
        · rw [hz, hy, e]
        · rw [pt_over, pt_over]
      · intro e
        have e' : spMap (τ : ℂ →+* ℂ) ≫ C.pt z = spMap (τ : ℂ →+* ℂ) ≫ C.pt y := by rw [← hz, ← hy, e]
        have := congrArg (spMap (τ.symm : ℂ →+* ℂ) ≫ ·) e'
        simpa only [← Category.assoc, spMap_symm, Category.id_comp] using this)
    (fun z z' y' hz e => by rw [← (hker _ _).2 e]; exact hz) n hn
  refine ⟨key.1.imp fun s hs => ⟨h, hs⟩, fun s hs => ⟨key.2 s hs.2, ?_⟩⟩
  rintro m ⟨k, rfl⟩
  refine ⟨h, fun a => ?_⟩
  have hk : (k : ℂ) ≠ 0 := by
    rintro hk
    have : k = 0 := by exact_mod_cast hk
    simp [this] at hn
  have e : wC H (k * a.1, k * a.2) = k * wC H a := by simp [wC]; ring
  have := hs.2 (k * a.1, k * a.2)
  rw [e] at this
  have hm : (m : ℂ) ≠ 0 := by
    rintro hk
    have : m = 0 := by exact_mod_cast hk
    simp [this] at hn
  have e1 : wC H s * (k * wC H a) / ((m * k : ℕ) : ℂ) = wC H s * wC H a / m := by push_cast; field_simp
  have e2 : (k * wC H a) / ((m * k : ℕ) : ℂ) = wC H a / m := by push_cast; field_simp
  rwa [e1, e2] at this

end GlobalTheory.CompRat.Acts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumSumAndAllSignatures
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DatumSum

noncomputable section

def blockEnd {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) : U →ₗ[ℝ] U :=
  e.symm.toLinearMap ∘ₗ (f.prodMap g) ∘ₗ e.toLinearMap

theorem blockEnd_apply {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) (x : U) :
    e (blockEnd e f g x) = (f (e x).1, g (e x).2) := by
  simp [blockEnd, Prod.map]

theorem blockEnd_comp {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f f' : V →ₗ[ℝ] V) (g g' : W →ₗ[ℝ] W) :
    blockEnd e f g ∘ₗ blockEnd e f' g' = blockEnd e (f ∘ₗ f') (g ∘ₗ g') := by
  ext x
  apply e.injective
  simp [blockEnd_apply]

theorem trace_blockEnd {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] [Module.Finite ℝ V] [Module.Finite ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) :
    LinearMap.trace ℝ U (blockEnd e f g) = LinearMap.trace ℝ V f + LinearMap.trace ℝ W g := by
  have h1 : blockEnd e f g = e.symm.conj (f.prodMap g) := by
    ext x; simp [blockEnd, LinearEquiv.conj_apply]
  rw [h1, LinearMap.trace_conj', LinearMap.trace_prodMap']

def sumForm {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) : LinearMap.BilinForm ℤ (L × M) :=
  B.compl₁₂ (LinearMap.fst ℤ L M) (LinearMap.fst ℤ L M) + C.compl₁₂ (LinearMap.snd ℤ L M) (LinearMap.snd ℤ L M)

theorem sumForm_apply {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (x y : L × M) : sumForm B C x y = B x.1 y.1 + C x.2 y.2 := by
  simp [sumForm]

theorem sumForm_bijective {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (hB : Function.Bijective B) (hC : Function.Bijective C) :
    Function.Bijective (sumForm B C) := by
  constructor
  · intro x y h
    refine Prod.ext (hB.1 ?_) (hC.1 ?_)
    · ext z
      have := LinearMap.congr_fun h (z, 0)
      simpa [sumForm_apply] using this
    · ext z
      have := LinearMap.congr_fun h (0, z)
      simpa [sumForm_apply] using this
  · intro φ
    obtain ⟨x, hx⟩ := hB.2 (φ ∘ₗ LinearMap.inl ℤ L M)
    obtain ⟨y, hy⟩ := hC.2 (φ ∘ₗ LinearMap.inr ℤ L M)
    refine ⟨(x, y), LinearMap.ext fun z => ?_⟩
    rw [sumForm_apply, hx, hy]
    simp [← map_add]

theorem sumForm_baseChange {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (x y : ℝ ⊗[ℤ] (L × M)) :
    (sumForm B C).baseChange ℝ x y =
      B.baseChange ℝ (TensorProduct.prodRight ℤ ℝ ℝ L M x).1 (TensorProduct.prodRight ℤ ℝ ℝ L M y).1 +
      C.baseChange ℝ (TensorProduct.prodRight ℤ ℝ ℝ L M x).2 (TensorProduct.prodRight ℤ ℝ ℝ L M y).2 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, Prod.fst_add, Prod.snd_add, ha, hb]; ring
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, Prod.fst_add, Prod.snd_add, ha, hb]; ring
    | tmul s v => simp [sumForm_apply, add_smul, add_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def sumDatum (D D' : Datum H) : Datum H where
  La := D.La × D'.La
  fin := by haveI := D.fin; haveI := D'.fin; infer_instance
  proj := by haveI := D.proj; haveI := D'.proj; infer_instance
  EF := sumForm D.EF D'.EF
  alt := fun x => by simp [sumForm_apply, D.alt, D'.alt]
  unimod := sumForm_bijective D.EF D'.EF D.unimod D'.unimod
  adj := fun a x y => by simp [sumForm_apply, D.adj, D'.adj]
  p := D.p + D'.p
  q := D.q + D'.q
  rank := by
    haveI := D.fin
    haveI := D.proj
    haveI := D'.fin
    haveI := D'.proj
    have h1 := (TensorProduct.isBaseChange (𝓞 E) (D.La × D'.La) E).finrank_eq
    have h2 := (TensorProduct.isBaseChange (𝓞 E) D.La E).finrank_eq
    have h2' := (TensorProduct.isBaseChange (𝓞 E) D'.La E).finrank_eq
    have h3 := (TensorProduct.prodRight (𝓞 E) E E D.La D'.La).finrank_eq
    rw [← h1, h3, Module.finrank_prod, h2, h2', D.rank, D'.rank]
    ring
  dom := by
    haveI := D.fin
    haveI := D'.fin
    haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    haveI : Module.Finite ℤ D'.La := Module.Finite.trans (𝓞 E) D'.La
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    obtain ⟨J', h1', h2', h3', h4'⟩ := D'.dom
    set e := TensorProduct.prodRight ℤ ℝ ℝ D.La D'.La with he
    refine ⟨blockEnd e J J', ?_, ?_, ?_, ?_⟩
    · intro x
      apply e.injective
      simp [blockEnd_apply, h1, h1', Prod.ext_iff]
    · intro x y
      simp only [sumForm_baseChange, ← he, blockEnd_apply, h2, h2']
    · intro x hx
      simp only [sumForm_baseChange, ← he, blockEnd_apply]
      have hne : e x ≠ 0 := fun hc => hx (e.injective (by rw [map_zero]; exact hc))
      by_cases ha : (e x).1 = 0
      · have hb : (e x).2 ≠ 0 := fun hb => hne (Prod.ext ha hb)
        simpa [ha] using h3' _ hb
      · by_cases hb : (e x).2 = 0
        · simpa [hb] using h3 _ ha
        · exact add_pos (h3 _ ha) (h3' _ hb)
    · intro a A t hA ht
      let A0 : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
        ((DistribMulAction.toAddMonoidHom D.La a).toIntLinearMap).baseChange ℝ
      let A1 : ℝ ⊗[ℤ] D'.La →ₗ[ℝ] ℝ ⊗[ℤ] D'.La :=
        ((DistribMulAction.toAddMonoidHom D'.La a).toIntLinearMap).baseChange ℝ
      obtain ⟨k1, k2, k3⟩ := h4 a A0 _ (fun x => by simp [A0]) rfl
      obtain ⟨k1', k2', k3'⟩ := h4' a A1 _ (fun x => by simp [A1]) rfl
      have hAA : A = blockEnd e A0 A1 := by
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp only [map_add, ha, hb]
        | tmul r u =>
          have : r ⊗ₜ[ℤ] u = r • ((1 : ℝ) ⊗ₜ[ℤ] u) := by simp [TensorProduct.smul_tmul']
          rw [this, map_smul, map_smul, hA]
          congr 1
          apply e.injective
          rw [blockEnd_apply]
          simp [he, A0, A1]
      have ht' : t = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
          ((D.p : ℂ) * τ (a : E) + (D.q : ℂ) * starRingEnd ℂ (τ (a : E))) +
          ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
          ((D'.p : ℂ) * τ (a : E) + (D'.q : ℂ) * starRingEnd ℂ (τ (a : E))) := by
        rw [ht, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        push_cast; ring
      rw [hAA, blockEnd_comp, blockEnd_comp, trace_blockEnd, trace_blockEnd, k1, ← k1, k1', ← k1', k2, k3, k2', k3',
        ht']
      refine ⟨rfl, ?_, ?_⟩
      · rw [Complex.add_re]; ring
      · rw [Complex.add_im]; ring

theorem finrank_cyclotomic_twenty_eight : Module.finrank ℚ CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight = 12 := by
  rw [IsCyclotomicExtension.finrank (n := 28) CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide

end

end GlobalTheory.DatumSum

namespace GlobalTheory

theorem exists_datum_sum_and_all_signatures :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H), ∃ (D'' : Datum H) (e : D''.La ≃ₗ[𝓞 E] D.La × D'.La), D''.p = D.p + D'.p ∧ D''.q = D.q + D'.q ∧ ∀ x y, D''.EF x y = D.EF (e x).1 (e y).1 + D'.EF (e x).2 (e y).2) ∧ ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E), 2 < Module.finrank ℚ E ∧ ∀ p q : ℕ, ∃ D : Datum H, D.p = p ∧ D.q = q := by
  refine ⟨fun E _ _ _ H D D' => ⟨DatumSum.sumDatum D D', LinearEquiv.refl (𝓞 E) (D.La × D'.La), rfl, rfl,
    fun x y => DatumSum.sumForm_apply D.EF D'.EF x y⟩, ?_⟩
  refine ⟨CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight, inferInstance, inferInstance, inferInstance, CM.CyclotomicTwentyEight.host, ?_, fun p q => ?_⟩
  · rw [DatumSum.finrank_cyclotomic_twenty_eight]; norm_num
  · obtain ⟨D, hp, hq⟩ := CM.CyclotomicTwentyEight.exists_datum
    refine ⟨DatumSum.sumDatum (powDatum D p) (powDatum (CM.oppDatum D) q), ?_, ?_⟩
    · change p * D.p + q * D.q = p
      simp [hp, hq]
    · change p * D.q + q * D.p = q
      simp [hp, hq]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cmData_sig_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : CMData F E) : ∃ a, hc.sig a ≠ a := by
  by_contra h
  push Not at h
  have hs : Function.Surjective (algebraMap F E) := fun a => (hc.fixed a).1 (h a)
  have h1 : Module.finrank F E = 1 :=
    (LinearEquiv.ofBijective (Algebra.linearMap F E)
      ⟨(algebraMap F E).injective, hs⟩).finrank_eq.symm.trans (Module.finrank_self F)
  have := hc.deg2
  omega

theorem exists_isDetRoot : ∀ (D : D7) (V : HSp D) (g : GA D V), ∃ x, IsDetRoot V g x := by
  intro D V g
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig
      (AlgHom.ext fun a => star_star a) (AlgHom.ext fun a => star_star a)
  have hc1 : c ≠ 1 := by
    obtain ⟨a, ha⟩ := cmData_sig_ne_id D.sp.cm
    intro h
    exact ha (congrArg (fun f : D.host.E ≃ₐ[D.host.F] D.host.E => f a) h)
  have hu := det_conj_mul V g
  rw [mul_comm] at hu
  exact GlobalTheory.AdLat.hilbert90_adeleRing_tensor_quadratic D.host.F D.host.E c D.sp.cm.deg2 hc1 (Formalism.L2.Theta.mt V g).det hu

end GlobalTheory.RecDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsModelPushInvertibleOverCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem exists_model_pushInvertible_under_cdvr : PartI → N1ab → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ), p.Prime → (p : T.V) ∈ IsLocalRing.maximalIdeal T.V → l.GoodAt p → ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L ∧ ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β := by
  intro hI hN E _ _ _ H Dw l Xo c hpos T io p hp hpT hg
  classical
  obtain ⟨Xf, hXf⟩ : ∃ Xf : ∀ l' : Level H, Moduli Dw l', Xf l = Xo :=
    ⟨Function.update (fun l' => (hN E H Dw l' hpos).some) l Xo, Function.update_self ..⟩
  subst hXf
  let U₀ : ValuationSubring T.Fr := (ValuationRing.valuation T.V T.Fr).valuationSubring
  have hU₀ : ∀ x : T.Fr, x ∈ U₀ ↔ ∃ a : T.V, algebraMap T.V T.Fr a = x := fun x =>
    ValuationRing.mem_integer_iff T.V T.Fr x
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  have hpU : (p : c.F) ∈ (U₀.comap io).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro h
    rw [ValuationSubring.mem_comap, hU₀] at h
    obtain ⟨a, ha⟩ := h
    have hp0 : (p : c.F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have h1 : a * (p : T.V) = 1 := by
      apply hinj
      rw [map_mul, ha, map_natCast, map_one, ← map_natCast io p, ← map_mul, inv_mul_cancel₀ hp0, map_one]
    exact (IsLocalRing.mem_maximalIdeal _).1 hpT (IsUnit.of_mul_eq_one_right a h1)
  obtain ⟨W, hW, hWU⟩ := GlobalTheory.T.exists_valuationSubring_complex_comap_eq c.F (U₀.comap io) p hpU
  obtain ⟨Y, hY, -⟩ := hI.2 E H Dw hpos Xf
  have hmem : ∀ x : c.V W, ∃ a : T.V, algebraMap T.V T.Fr a = io x := by
    intro x
    have hx : (x : c.F) ∈ U₀.comap io := hWU ▸ x.2
    exact (hU₀ _).1 (ValuationSubring.mem_comap.1 hx)
  choose f hf using hmem
  refine ⟨c.V W, inferInstance, (c.V W).subtype, Y p W hp hW ⟨l, c, hg⟩,
    ((hY p W hp hW).1.1 ⟨l, c, hg⟩).2.2.1, ?_⟩
  refine ⟨{ toFun := f
            map_one' := hinj (by simp [hf])
            map_mul' := fun x y => hinj (by simp [hf])
            map_zero' := hinj (by simp [hf])
            map_add' := fun x y => hinj (by simp [hf]) }, ?_⟩
  ext x
  exact hf x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatCuspExpo
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

theorem lat_cusp_expo : GlobalTheory.Published.HasseNormSt → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → FJ.LatZ M.X (WeightFamilies.rho D j) ∧ FJ.CuNeF M.X (WeightFamilies.rho D j) ∧ FJ.ExpoMatch M.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1) := by
  intro HN D Q hQ j hj σ' g ty F _ _ M io th x₀ hM
  refine ⟨GlobalTheory.CuspCentre.latZ _ _ _ _ _, fun k => ?_, ?_⟩
  · have hp : (M.X k).p0 = D.R.m - j := ((hM.1.type k).1).trans (hQ.2.2.2 j hj).2.1
    have hρ : WeightFamilies.rho D j = D.R.m - j := rfl
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    have hk := D.R.m_add_three_le_k
    have h1 := hj.1
    have h2 := hj.2
    exact GlobalTheory.CuspExist.nonempty_cuspFD HN _ _ _ _ (by omega) (by omega) (by omega)
  · rw [← hQ.2.1.1]
    exact GlobalTheory.ExpoModels.expoMatch_models _ _ _ _ _ _ _ _ F _ M _ hM.1 hQ.2.1.2

end GlobalTheory.RecDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValVEqOneIntegralGeneratorsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valV_eq_one_integral_generators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y y' : FrPt Xo c T.Fr) (G G₂ : SAB H (Sp T.V)) (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t y.x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t₂ Xo.univ.t y'.x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), y'.x = y.x → k.φ ≫ n₁.φ = m₁.φ → m₂.φ ≫ n.φ = k.φ ≫ n₂.φ → ∀ (θ : LB.Sec G.PP.L) (θ₂ : LB.Sec G₂.PP.L), ((∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m₁.φ)) (w2 : LB.Iso t.PP.L (G.PP.L.pull m₂.φ)) (σ : LB.Sec t.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m₁.φ)) (θ2 : LB.Sec (G.PP.L.pull m₂.φ)), RigIso m₁ w1 ∧ RigIso m₂ w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m₂.φ θ θ2 ∧ ∀ g : t.G.left ⟶ Gx y.x, g ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = m₁.φ → g ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = t.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m₁.φ).U j ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (y.s.f (fun _ => j PUnit.unit))) → ((∀ σ : LB.Sec G₂.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G₂.G.left (le_top : G₂.PP.L.U i ≤ ⊤) ((G₂.G.hom).appTop.hom (toΓ T.V a)) * θ₂.f i) ∧ ∃ (w1 : LB.Iso t₂.PP.L (Xo.univ.t.PP.L.pull n₁.φ)) (w2 : LB.Iso t₂.PP.L (G₂.PP.L.pull n₂.φ)) (σ : LB.Sec t₂.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull n₁.φ)) (θ2 : LB.Sec (G₂.PP.L.pull n₂.φ)), RigIso n₁ w1 ∧ RigIso n₂ w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec n₂.φ θ₂ θ2 ∧ ∀ g : t₂.G.left ⟶ Gx y'.x, g ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = n₁.φ → g ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = t₂.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull n₁.φ).U j ≤ g ⁻¹ᵁ (PPx y'.x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (y'.s.f (fun _ => j PUnit.unit))) → ∀ a : T.Frˣ, SecBC (RingHom.id T.Fr) (a : T.Fr) y.x y'.x y.s y'.s → valV T.V (a : T.Fr) = 1 := by
  first | exact @GlobalTheory.IntegralGenerator.valV_eq_one | exact GlobalTheory.IntegralGenerator.valV_eq_one | (intros; apply GlobalTheory.IntegralGenerator.valV_eq_one <;> assumption)
end

