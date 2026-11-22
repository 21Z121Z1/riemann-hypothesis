import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0210

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorProductDefiniteUnitaryLocalModelsIrreducib
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift

theorem subalgebra_eq_top_of_irreducible {X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (A : Subalgebra ℂ (Module.End ℂ X))
    (h : ∀ U : Submodule ℂ X, (∀ a ∈ A, ∀ x ∈ U, a x ∈ U) → U = ⊥ ∨ U = ⊤) : A = ⊤ := by
  classical
  rcases subsingleton_or_nontrivial X with hX | hX
  · refine eq_top_iff.2 fun f _ => ?_
    rw [Subsingleton.elim f 0]
    exact A.zero_mem
  haveI : IsSimpleModule A X := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun U => ?_ }
    rcases h (U.restrictScalars ℂ) (fun a ha x hx => U.smul_mem (⟨a, ha⟩ : A) hx) with h1 | h1
    · left
      exact (Submodule.restrictScalars_eq_bot_iff ℂ A X).1 h1
    · right
      exact (Submodule.restrictScalars_eq_top_iff ℂ A X).1 h1
  have hscal : ∀ φ : Module.End A X, ∃ c : ℂ, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := X) ℂ).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  refine eq_top_iff.2 fun f _ => ?_
  let F : Module.End (Module.End A X) X :=
    { toFun := fun m => f m
      map_add' := fun x y => by simp
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hscal φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  let b := Module.finBasis ℂ X
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  have : f = (r : Module.End ℂ X) :=
    b.ext fun i => hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]
  exact r.2

theorem piTensor_irreducible {ι κ : Type} [Finite ι] [DecidableEq ι] {H : ι → Type} [∀ i, AddCommGroup (H i)]
    [∀ i, Module ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)] (σ : ∀ i, κ → Module.End ℂ (H i))
    (h : ∀ i, ∀ U : Submodule ℂ (H i), (∀ u, ∀ x ∈ U, σ i u x ∈ U) → U = ⊥ ∨ U = ⊤)
    (U : Submodule ℂ (⨂[ℂ] i, H i))
    (hU : ∀ i u, ∀ x ∈ U,
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i (σ i u)) x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  cases nonempty_fintype ι
  have hcomp : ∀ (f g : ∀ i, H i →ₗ[ℂ] H i) (x : ⨂[ℂ] i, H i),
      PiTensorProduct.map (fun i => f i ∘ₗ g i) x = PiTensorProduct.map f (PiTensorProduct.map g x) := by
    intro f g x
    rw [PiTensorProduct.map_comp]; rfl
  have h1 : ∀ i (a : Module.End ℂ (H i)), ∀ x ∈ U,
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i a) x ∈ U := by
    intro i
    let A : Subalgebra ℂ (Module.End ℂ (H i)) :=
      { carrier := {a | ∀ x ∈ U,
          PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i a) x ∈ U}
        mul_mem' := fun {a b} ha hb x hx => by
          have := ha _ (hb x hx)
          rw [← hcomp] at this
          convert this using 3
          funext ρ
          by_cases hρ : ρ = i
          · subst hρ; simp [Module.End.mul_eq_comp]
          · simp [Function.update_of_ne hρ]
        add_mem' := fun {a b} ha hb x hx => by
          rw [PiTensorProduct.map_update_add]
          exact U.add_mem (ha x hx) (hb x hx)
        algebraMap_mem' := fun c x hx => by
          rw [Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul]
          have : Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i (1 : Module.End ℂ (H i)) =
              fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ) := Function.update_eq_self i _
          rw [this, PiTensorProduct.map_id]
          exact U.smul_mem c hx }
    have hA : A = ⊤ := subalgebra_eq_top_of_irreducible A fun W hW =>
      h i W fun u x hx => hW (σ i u) (hU i u) x hx
    intro a
    have : a ∈ A := hA ▸ Algebra.mem_top
    exact this
  have h2 : ∀ (f : ∀ i, H i →ₗ[ℂ] H i) (s : Finset ι), ∀ x ∈ U,
      PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) x ∈ U := by
    intro f s
    induction s using Finset.induction_on with
    | empty => intro x hx; simpa using hx
    | insert j s hj ih =>
      intro x hx
      have := h1 j (f j) _ (ih x hx)
      rw [← hcomp] at this
      convert this using 3
      funext ρ
      by_cases hρ : ρ = j
      · subst hρ; simp [hj]
      · simp [hρ]
  have h3 : ∀ (f : ∀ i, H i →ₗ[ℂ] H i), ∀ x ∈ U, PiTensorProduct.map f x ∈ U := by
    intro f x hx
    simpa using h2 f Finset.univ x hx
  rw [or_iff_not_imp_left]
  intro hne
  obtain ⟨x, hxU, hx⟩ := (Submodule.ne_bot_iff U).1 hne
  let b := fun i => Module.finBasis ℂ (H i)
  let B := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, B.repr x p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (B.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have e : PiTensorProduct.map (fun i => ((b i).coord (p i)).smulRight (v i)) =
      (B.coord p).smulRight (PiTensorProduct.tprod ℂ v) := by
    ext w
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.smulRight_apply,
      Module.Basis.coord_apply, B, Basis.piTensorProduct_repr_tprod_apply]
    exact (PiTensorProduct.tprod ℂ).map_smul_univ _ v
  have h4 := h3 (fun i => ((b i).coord (p i)).smulRight (v i)) x hxU
  rw [e] at h4
  exact (U.smul_mem_iff hp).1 h4

theorem tensor_irreducible : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧ ∀ U : Submodule ℂ (M.H τ), (∀ u : Matrix.unitaryGroup (Fin V.rank) ℂ, ∀ x ∈ U, M.σ τ u x ∈ U) → U = ⊥ ∨ U = ⊤) → AllPlus M → FiniteDimensional ℂ (SmT M) ∧ Function.Injective (inclT M) ∧ ∃ π, IsTensAct M π ∧ IrrFam π := by
  intro D V S M h _
  classical
  haveI := fun τ => (h τ).1
  let e : SmT M ≃ₗ[ℂ] ⨂[ℂ] τ, M.H τ := PiTensorProduct.congr fun τ => LinearEquiv.ofTop (M.sm τ) (h τ).2.1
  have he : ∀ x, e x = inclT M x := fun x => rfl
  refine ⟨inferInstance, fun x y hxy => e.injective hxy,
    fun τ u => e.symm.toLinearMap ∘ₗ actT M τ (unfr M τ u) ∘ₗ e.toLinearMap, fun τ u x => ?_, fun U hU => ?_⟩
  · rw [← he, ← he]
    simp
  · have := piTensor_irreducible (fun τ (u : Matrix.unitaryGroup (Fin V.rank) ℂ) => (M.σ τ u : M.H τ →ₗ[ℂ] M.H τ))
      (fun τ => (h τ).2.2) (U.map e.toLinearMap) (by
        rintro τ u _ ⟨x, hx, rfl⟩
        refine ⟨_, hU τ u x hx, ?_⟩
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, actT, rep_unfr])
    rcases this with h1 | h1
    · exact Or.inl ((Submodule.map_eq_bot_iff).1 h1)
    · exact Or.inr ((Submodule.map_eq_top_iff).1 h1)

end GlobalTheory.DefLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardLevelMoveIncidenceOfPairs
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke

section
variable {R V k W W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]
  [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']

theorem mem_loc_map_equiv (res : R →+* k) (g : V ≃ₗ[R] V) (M : Submodule R V) (y : V) :
    y ∈ loc res (M.map (g : V →ₗ[R] V)) ↔ g.symm y ∈ loc res M := by
  rw [mem_loc, mem_loc]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [Submodule.mem_map_equiv, map_smul]

theorem act_pairOf_value (res : R →+* k) (g : V ≃ₗ[R] V) (M M' : Submodule R V) (pr : M →+ W) (pr' : M' →+ W')
    (φ : Module.Dual k W) (φ' : Module.Dual k W')
    (hs : ∀ (a : R) z, pr (a • z) = res a • pr z) (hs' : ∀ (a : R) z, pr' (a • z) = res a • pr' z)
    (t : R) (z : M) (e : V) (he : t • e = z.1) (h1 : φ (pr z) = 1)
    (hm : e ∈ loc res (M'.map (g : V →ₗ[R] V)))
    (h : ∀ (x : M') (hx : t • g x.1 ∈ M), φ' (pr' x) = φ (pr ⟨_, hx⟩)) :
    ((pairOf res M' pr' φ').act g).f e = 1 := by
  rw [mem_loc_map_equiv] at hm
  obtain ⟨s, hs0, hx⟩ := (mem_loc _ _ _).1 hm
  have e1 : t • g (s • g.symm e) = (s • z : M).1 := by
    rw [map_smul, g.apply_symm_apply, smul_comm, he]; rfl
  have hx2 : t • g (s • g.symm e) ∈ M := by rw [e1]; exact (s • z).2
  have h2 := h ⟨_, hx⟩ hx2
  have e2 : (⟨_, hx2⟩ : M) = s • z := Subtype.ext e1
  rw [locExt_spec res M' pr' hs' _ hm s hx, map_smul, e2, hs, map_smul, h1] at h2
  show φ' (locExt res M' pr' (g.symm e)) = 1
  exact smul_right_injective k hs0 h2

end

set_option maxHeartbeats 1000000 in
theorem up_move_incidence : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (z : ↥(Ld D u i hi c)) (γ : GL (Fin (D.R.N i)) D.host.E), (D.fm u).fv i v c (P.pr v c z) = 1 → loc (A.res v) (mulLat γ.1 (clsCrd D u i hi c')) = loc (A.res v) (Ld D u i hi c) → loc (A.res v) (mulLat γ.1 (Ld D u i hi c')) = loc (A.res v) (Ld D u i hi c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) → (∀ (x : ↥(Ld D u i hi c')) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1 *ᵥ x.1) ∈ Ld D u i hi c), (D.fm u).fv i v c' (P.pr v c' x) = (D.fm u).fv i v c (P.pr v c ⟨_, hx⟩)) → ((pc P v c').act (glE γ)).IsKer (pc P v c).L ∧ ∃ e, ((pc P v c').act (glE γ)).f e = 1 ∧ locExt (A.res v) (Ld D u i hi c) (P.pr v c) ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • e) = P.pr v c z := by
  intro D u A i hi P K v c c' z γ h1 h2 h3 h4
  have hT : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have he : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1) = z.1 := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hT, one_smul]
  refine ⟨fun y => ?_, (((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1, ?_, ?_⟩
  · rw [Pr.mem_act]
    have h5 := pc_isKer P K v c' ((glE γ).symm y)
    rw [GlobalTheory.T.classLattice_sup_primeDual_localization_eq D u A i hi K v c', ← mem_loc_map_equiv, map_glE, h2] at h5
    exact h5
  · refine act_pairOf_value (A.res v) (glE γ) _ _ (P.pr v c) (P.pr v c') _ _ (P.pr_smul v c) (P.pr_smul v c')
      _ z _ he h1 ?_ h4
    rw [map_glE, h3]
    exact le_loc _ _ (Submodule.mem_sup_right (Submodule.subset_span rfl))
  · rw [he]; exact locExt_coe _ _ _ (P.pr_smul v c) z

end GlobalTheory.LevelHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WittTheoremAdelicOneVector
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.AdelicWitt

theorem qR_ratTup {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (b : Module.Basis (Fin 2) F E) (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F)
    (h : hE σ J (x 0) (x 0) = algebraMap F E β) :
    qR R σ J (ratTup (F := F) R x 0) = algebraMap F R β := by
  have h1 : hR R σ J (ratTup (F := F) R x 0) (ratTup (F := F) R x 0) =
      inclR (F := F) R (hE σ J (x 0) (x 0)) := by
    simp only [hR, hE, Formalism.UG.hform, map_sum, map_mul, ratTup, JR, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 2
  have h2 : inclR (F := F) R (algebraMap F E β) = algebraMap R (R ⊗[F] E) (algebraMap F R β) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes β
  rw [qR, h1, h, h2, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b),
    Fintype.card_fin, ← map_nsmul, ← map_mul]
  congr 1
  rw [nsmul_eq_mul]; push_cast; field_simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem prInf_sigR (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) :
    prInf (sigR (AF F) σ z) = sigR (Ainf F) σ (prInf z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add a c ha hc => simp only [map_add, ha, hc]

omit [NumberField E] in
theorem prV_sigR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    prV v (sigR (AF F) σ z) = sigR (Fv F v) σ (prV v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add a c ha hc => simp only [map_add, ha, hc]

omit [NumberField E] in
theorem prInf_inclR (e : E) : prInf (inclR (F := F) (AF F) e) = inclR (F := F) (Ainf F) e := by
  simp [prInf, inclR]

omit [NumberField E] in
theorem prV_inclR (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV v (inclR (F := F) (AF F) e) = inclR (F := F) (Fv F v) e := by
  simp [prV, inclR]

theorem ext_comp {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ} (X Y : Fin n → Fin M → AF F ⊗[F] E)
    (hi : ∀ a i, prInf (X a i) = prInf (Y a i))
    (hv : ∀ (v : HeightOneSpectrum (𝓞 F)) a i, prV v (X a i) = prV v (Y a i)) : X = Y := by
  apply (GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M).1.injective
  refine Prod.ext ?_ ?_
  · funext a i; exact hi a i
  · funext v a i; exact hv v a i

theorem mat_ext {d : ℕ} (b : Module.Basis (Fin d) F E) {M : ℕ}
    (X Y : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
    (hi : X.map prInf = Y.map prInf)
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), X.map (prV v) = Y.map (prV v)) : X = Y :=
  ext_comp b X Y (fun a i => congrFun (congrFun hi a) i) (fun v a i => congrFun (congrFun (hv v) a) i)

theorem exists_mat {d : ℕ} (b : Module.Basis (Fin d) F E) {M : ℕ}
    (Xi : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E))
    (Xv : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E))
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, Xv v i j ∈ intV b v) :
    ∃ X : Matrix (Fin M) (Fin M) (AF F ⊗[F] E), X.map prInf = Xi ∧ ∀ v, X.map (prV v) = Xv v := by
  have := ((Set.ext_iff.1 (GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b M M).2.1) (Xi, Xv)).2 h
  obtain ⟨X, hX⟩ := this
  exact ⟨X, congrArg Prod.fst hX, fun v => congrFun (congrArg Prod.snd hX) v⟩

theorem map_unit {A B : Type} [CommRing A] [CommRing B] {M : ℕ} (φ : A →+* B) (s : A →+* A)
    (t : B →+* B) (h : ∀ z, φ (s z) = t (φ z)) (X J : Matrix (Fin M) (Fin M) A) :
    (Formalism.UG.cT s X * J * X).map φ = Formalism.UG.cT t (X.map φ) * J.map φ * X.map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  exact h _

theorem exists_HA {d : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (gi : HA (Ainf F) σ J)
    (gv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j,
      (HA.mat (Fv F v) σ J (gv v)).val i j ∈ intV b v ∧
        (HA.mat (Fv F v) σ J (gv v)⁻¹).val i j ∈ intV b v) :
    ∃ g : HA (AF F) σ J, (HA.mat (AF F) σ J g).val.map prInf = (HA.mat (Ainf F) σ J gi).val ∧
      ∀ v, (HA.mat (AF F) σ J g).val.map (prV v) = (HA.mat (Fv F v) σ J (gv v)).val := by
  obtain ⟨X, hXi, hXv⟩ := exists_mat b (HA.mat (Ainf F) σ J gi).val
    (fun v => (HA.mat (Fv F v) σ J (gv v)).val) (h.mono fun v hv i j => (hv i j).1)
  obtain ⟨Y, hYi, hYv⟩ := exists_mat b (HA.mat (Ainf F) σ J gi).inv
    (fun v => (HA.mat (Fv F v) σ J (gv v)).inv) (h.mono fun v hv i j => (hv i j).2)
  have hXY : X * Y = 1 := by
    refine mat_ext b _ _ ?_ fun v => ?_
    · rw [Matrix.map_mul, hXi, hYi, Units.val_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, hXv, hYv, Units.val_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hYX : Y * X = 1 := by
    refine mat_ext b _ _ ?_ fun v => ?_
    · rw [Matrix.map_mul, hXi, hYi, Units.inv_val, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, hXv, hYv, Units.inv_val, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJi : (JR (F := F) (AF F) J).map prInf = JR (F := F) (Ainf F) J := by
    ext i j; exact prInf_inclR _
  have hJv : ∀ v, (JR (F := F) (AF F) J).map (prV v) = JR (F := F) (Fv F v) J := by
    intro v; ext i j; exact prV_inclR v _
  have hU : Formalism.UG.cT (sigR (AF F) σ) X * JR (F := F) (AF F) J * X = JR (F := F) (AF F) J := by
    refine mat_ext b _ _ ?_ fun v => ?_
    · rw [map_unit _ _ _ (prInf_sigR σ), hXi, hJi]
      exact (show HR (Ainf F) σ J from gi).2
    · rw [map_unit _ _ _ (prV_sigR σ v), hXv, hJv]
      exact (show HR (Fv F v) σ J from gv v).2
  exact ⟨(show HR (AF F) σ J from ⟨⟨X, Y, hXY, hYX⟩, hU⟩), hXi, hXv⟩

theorem witt_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ y : (Fin 1 → Fin M → AF F ⊗[F] E), qR (AF F) σ J (y 0) = algebraMap F (AF F) β → ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y := by
  intro F E _ _ _ _ _ σ hCM M J x β hJ hβ hx y hy
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hCM.2.2.1
  obtain ⟨hyi, hyv⟩ := ((GlobalTheory.T.hermitianQuadratic_unitary_local_components F E σ M J).1 (y 0) β).1 hy
  have hu : IsUnit β := hβ.isUnit
  obtain ⟨gi, hgi⟩ := GlobalTheory.T.cmExtension_localFieldProductRing_exists_smul_eq F E σ hCM (Ainf F) (GlobalTheory.T.isNiceLocalFieldProductRing_infiniteAdeles_completions F).1 M J hJ
    (algebraMap F _ β) (ratTup (F := F) (Ainf F) x) (projInf y) (hu.map _)
    (qR_ratTup b _ σ J x β hx) hyi
  have hlat : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, projV v (projFin y) ∈ latV b v := by
    have h := (GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E 2 b 1 M).2.1 ▸ Set.mem_range_self (f := fun X : (Fin 1 → Fin M → AF F ⊗[F] E) =>
      (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) y
    exact h
  have hae := GlobalTheory.T.integral_witt_theorem_almost_all_places F E σ hCM 2 b M J x β hJ hβ hx
  let P : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J → Prop := fun v g => ∀ i j,
      (HA.mat (Fv F v) σ J g).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J g⁻¹).val i j ∈ intV b v
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g : HA (Fv F v) σ J,
      g • ratTup (F := F) (Fv F v) x = projV v (projFin y) ∧
      ((∃ g' : HA (Fv F v) σ J, g' • ratTup (F := F) (Fv F v) x = projV v (projFin y) ∧ P v g') →
        P v g) := by
    intro v
    by_cases h : ∃ g' : HA (Fv F v) σ J,
        g' • ratTup (F := F) (Fv F v) x = projV v (projFin y) ∧ P v g'
    · obtain ⟨g, h1, h2⟩ := h
      exact ⟨g, h1, fun _ => h2⟩
    · obtain ⟨g, hg⟩ := GlobalTheory.T.cmExtension_localFieldProductRing_exists_smul_eq F E σ hCM (Fv F v) ((GlobalTheory.T.isNiceLocalFieldProductRing_infiniteAdeles_completions F).2 v) M J hJ
        (algebraMap F _ β) (ratTup (F := F) (Fv F v) x) (projV v (projFin y)) (hu.map _)
        (qR_ratTup b _ σ J x β hx) (hyv v)
      exact ⟨g, hg, fun h' => absurd h' h⟩
  choose gv hgv hP using hloc
  obtain ⟨g, hi, hv⟩ := exists_HA b σ J gi gv (by
    filter_upwards [hlat, hae] with v h1 h2
    exact hP v (h2 _ h1 (hyv v)))
  refine ⟨g, ext_comp b _ _ (fun a i => ?_) (fun v a i => ?_)⟩
  · have h1 := congrFun (congrFun hgi a) i
    rw [projInf_apply] at h1
    rw [← h1]
    show prInf ((HA.mat (AF F) σ J g).val.mulVec (ratTup (F := F) (AF F) x a) i) =
      (HA.mat (Ainf F) σ J gi).val.mulVec (ratTup (F := F) (Ainf F) x a) i
    rw [RingHom.map_mulVec, hi]
    exact congrArg (fun w => (HA.mat (Ainf F) σ J gi).val.mulVec w i)
      (funext fun k => prInf_inclR (x a k))
  · have h1 := congrFun (congrFun (hgv v) a) i
    rw [projV_apply] at h1
    rw [← h1]
    show prV v ((HA.mat (AF F) σ J g).val.mulVec (ratTup (F := F) (AF F) x a) i) =
      (HA.mat (Fv F v) σ J (gv v)).val.mulVec (ratTup (F := F) (Fv F v) x a) i
    rw [RingHom.map_mulVec, hv]
    exact congrArg (fun w => (HA.mat (Fv F v) σ J (gv v)).val.mulVec w i)
      (funext fun k => prV_inclR v (x a k))

end GlobalTheory.AdelicWitt
end

