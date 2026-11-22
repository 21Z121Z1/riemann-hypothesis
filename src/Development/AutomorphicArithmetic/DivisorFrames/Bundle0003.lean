import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1070

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.CokernelFrameCompatMono
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.Twist (resM)

private theorem hom_ext_frame {X : Scheme.{0}} {F G : X.Modules} {κ : Type} [Fintype κ] {e : κ → Γ(F, ⊤)}
    (he : IsFrame e) {φ ψ : F ⟶ G} (h : ∀ i, φ.app ⊤ (e i) = ψ.app ⊤ (e i)) : φ = ψ := by
  ext V s
  refine congr($((he.basis le_top).ext (f₁ := QCoh.appLinear φ V) (f₂ := QCoh.appLinear ψ V)
    fun i => ?_) s)
  rw [IsFrame.basis_apply]
  exact (Twist.app_resM φ _ _).trans ((congrArg _ (h i)).trans (Twist.app_resM ψ _ _).symm)

theorem UpperTheory.cokernel_frame_compat_mono :
    ∀ (X : Scheme.{0}) (E A A' : X.Modules) (u : A ⟶ E) (v : A' ⟶ E) (m r : ℕ) (e : Fin m ⊕ Fin r → Γ(E, ⊤))
        (a : Fin m → Fin r → Γ(X, ⊤)), Mono u → Mono v → IsFrame e →
        IsFrame (fun k => (cokernel.π u).app ⊤ (e (Sum.inr k))) →
        (∀ i, (cokernel.π u).app ⊤ (e (Sum.inl i)) = ∑ k, a i k • (cokernel.π u).app ⊤ (e (Sum.inr k))) →
        IsFrame (fun k => (cokernel.π v).app ⊤ (e (Sum.inr k))) →
        (∀ i, (cokernel.π v).app ⊤ (e (Sum.inl i)) = ∑ k, a i k • (cokernel.π v).app ⊤ (e (Sum.inr k))) →
        ∃ φ : A ≅ A', φ.hom ≫ v = u := by
  intro X E A A' u v m r e a hu hv he fu au fv av
  have key : cokernel.π u ≫ (IsFrame.iso fu fv).hom = cokernel.π v := by
    refine hom_ext_frame he fun i => ?_
    rw [← QCoh.app_app]
    rcases i with i | k
    · rw [au, av]
      refine (map_sum (QCoh.appLinear (IsFrame.iso fu fv).hom ⊤) _ _).trans
        (Finset.sum_congr rfl fun k _ => ?_)
      rw [map_smul]
      exact congrArg _ (IsFrame.iso_hom_app fu fv k)
    · exact IsFrame.iso_hom_app fu fv k
  have h1 : u ≫ cokernel.π v = 0 := by
    rw [← key, ← Category.assoc, cokernel.condition, zero_comp]
  have h2 : v ≫ cokernel.π u = 0 := by
    rw [← cancel_mono (IsFrame.iso fu fv).hom, Category.assoc, key, cokernel.condition, zero_comp]
  have hf := Abelian.monoLift_comp v u h1
  have hg := Abelian.monoLift_comp u v h2
  exact ⟨⟨Abelian.monoLift v u h1, Abelian.monoLift u v h2,
    by rw [← cancel_mono u, Category.assoc, hg, hf, Category.id_comp],
    by rw [← cancel_mono v, Category.assoc, hf, hg, Category.id_comp]⟩, hf⟩
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsSubbundleCokernelFrame
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.Twist (resM)

private theorem UpperTheory.frame_defines_endomorphism {X : Scheme.{0}} {E : X.Modules} {ι : Type} [Fintype ι]
    {e : ι → Γ(E, ⊤)} (he : IsFrame e) (q : ι → Γ(E, ⊤)) :
    ∃ p : E ⟶ E, ∀ j, p.app ⊤ (e j) = q j := by
  refine ⟨LB.homOfLinear (fun V => (he.basis (le_top : V ≤ ⊤)).constr ℕ
    (fun j => resM E (le_top : V ≤ ⊤) (q j))) ?_, fun j => ?_⟩
  · intro V W h s
    have key (V : X.Opens) (j : ι) : (he.basis (le_top : V ≤ ⊤)).constr ℕ
        (fun j => resM E (le_top : V ≤ ⊤) (q j)) (resM E le_top (e j)) = resM E le_top (q j) := by
      rw [← he.basis_apply, Module.Basis.constr_basis]
    obtain ⟨c, rfl⟩ := (he V le_top).2 s
    change (he.basis (le_top : W ≤ ⊤)).constr ℕ (fun j => resM E (le_top : W ≤ ⊤) (q j)) (resM E h _) =
      resM E h _
    simp only [Fintype.linearCombination_apply, map_sum, Twist.resM_smul, Twist.resM_resM,
      map_smul, key]
  · rw [LB.homOfLinear_app]
    have := (he.basis (le_top : (⊤ : X.Opens) ≤ ⊤)).constr_basis ℕ
      (fun j => resM E (le_top : (⊤ : X.Opens) ≤ ⊤) (q j)) j
    rwa [he.basis_apply, Twist.resM_self, Twist.resM_self] at this

theorem UpperTheory.exists_subbundle_cokernel_frame :
    ∀ (X : Scheme.{0}) (E : X.Modules) (m r : ℕ) (e : Fin m ⊕ Fin r → Γ(E, ⊤)) (a : Fin m → Fin r → Γ(X, ⊤)),
        IsFrame e → ∃ N : GlobalTheory.VB.Sub E, IsFrame (fun k => (cokernel.π N.incl).app ⊤ (e (Sum.inr k))) ∧
          ∀ i, (cokernel.π N.incl).app ⊤ (e (Sum.inl i)) = ∑ k, a i k • (cokernel.π N.incl).app ⊤ (e (Sum.inr k)) := by
  intro X E m r e a he
  obtain ⟨p, hp⟩ := UpperTheory.frame_defines_endomorphism he
    (Sum.elim (fun i => ∑ k, a i k • e (Sum.inr k)) (fun k => e (Sum.inr k)))
  have hr (k : Fin r) : p.app ⊤ (e (Sum.inr k)) = e (Sum.inr k) := hp _
  have hl (i : Fin m) : p.app ⊤ (e (Sum.inl i)) = ∑ k, a i k • e (Sum.inr k) := hp _
  have hz (V : X.Opens) (s : Γ(E, V)) :
      (cokernel.π (Sub.ker p).incl).app V s = 0 ↔ p.app V s = 0 :=
    (Sub.ker p).cokernel_π_app_eq_zero_iff
  have h2 (i : Fin m) : (cokernel.π (Sub.ker p).incl).app ⊤ (e (Sum.inl i)) =
      ∑ k, a i k • (cokernel.π (Sub.ker p).incl).app ⊤ (e (Sum.inr k)) := by
    simp only [← Scheme.Modules.Hom.app_smul]
    rw [← map_sum, ← sub_eq_zero, ← map_sub, hz, map_sub, hl, map_sum]
    simp only [Scheme.Modules.Hom.app_smul, hr, sub_self]
  refine ⟨Sub.ker p, ?_, h2⟩
  have hgen (V : X.Opens) (h : V ≤ ⊤) (s : Γ(E, V)) : (cokernel.π (Sub.ker p).incl).app V s ∈
      Submodule.span Γ(X, V) (Set.range fun k =>
        resM _ h ((cokernel.π (Sub.ker p).incl).app ⊤ (e (Sum.inr k)))) := by
    obtain ⟨c, rfl⟩ := (he V h).2 s
    rw [Fintype.linearCombination_apply, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Scheme.Modules.Hom.app_smul, Twist.app_resM]
    refine Submodule.smul_mem _ _ ?_
    rcases j with i | k
    · rw [h2, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [Twist.resM_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · exact Submodule.subset_span ⟨k, rfl⟩
  have hpp (V : X.Opens) (s : Γ(E, V)) : p.app V (p.app V s) = p.app V s := by
    obtain ⟨c, rfl⟩ := (he V le_top).2 s
    simp only [Fintype.linearCombination_apply, map_sum, Scheme.Modules.Hom.app_smul,
      Twist.app_resM]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases j with i | k
    · simp only [hl, map_sum, Scheme.Modules.Hom.app_smul, hr]
    · simp only [hr]
  have h0 : (Sub.ker p).incl ≫ p = 0 := by
    refine Scheme.Modules.hom_ext _ _ fun V => ?_
    ext s
    exact (QCoh.app_app _ _ V s).symm.trans ((Sub.ker p).incl_app_mem s)
  have h1 : cokernel.desc _ p h0 ≫ cokernel.π (Sub.ker p).incl = 𝟙 _ := by
    rw [← cancel_epi (cokernel.π (Sub.ker p).incl), cokernel.π_desc_assoc, Category.comp_id]
    refine Scheme.Modules.hom_ext _ _ fun V => ?_
    ext s
    refine (QCoh.app_app _ _ V s).symm.trans ?_
    change _ = (cokernel.π (Sub.ker p).incl).app V s
    rw [← sub_eq_zero, ← map_sub, hz, map_sub, hpp, sub_self]
  refine isFrame_iff.2 fun V h => ⟨?_, fun t _ => ?_⟩
  · have hli := ((isFrame_iff.1 he V h).1).comp Sum.inr Sum.inr_injective
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc
    apply hli c
    simp only [← Twist.app_resM, ← Scheme.Modules.Hom.app_smul] at hc
    rw [← map_sum, hz, map_sum] at hc
    simpa only [Scheme.Modules.Hom.app_smul, Twist.app_resM, hr, Function.comp_apply] using hc
  · have := hgen V h ((cokernel.desc _ p h0).app V t)
    rwa [QCoh.app_app, h1] at this
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.FrameExtendsFromPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.Twist (resM)

theorem UpperTheory.frame_extends_from_pullback :
    ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (Q : X.Modules) (r : ℕ) (U : X.Opens) (s : Fin r → Γ(Q, U)) (V : Y.Opens)
        (h : V ≤ f ⁻¹ᵁ U) (y : Y), IsVB Q r → y ∈ V → IsFrame (fun k => pullbackSections f Q h (s k)) →
        ∃ (W : X.Opens) (hW : W ≤ U), f y ∈ W ∧ IsFrame fun k => resM Q hW (s k) := by
  intro X Y f Q r U s V h y hQ hy hs
  classical
  have := hQ.isQuasicoherent
  obtain ⟨U', c, -, hx, hle, hc⟩ := hQ.exists_affine (h hy : f y ∈ U)
  set v : Fin r → Γ(Q, U') := fun k => resM Q hle (s k) with hv
  have hT : V ⊓ f ⁻¹ᵁ U' ≤ f ⁻¹ᵁ U' := inf_le_right
  have hu : IsUnit (f.appLE U' _ hT ((hc.basis le_rfl).det v)) := by
    have h1 := hs (V ⊓ f ⁻¹ᵁ U') inf_le_left
    rw [Ker.bijective_iff_isUnit_det ((hc.pullback f).basis (hT.trans (f.preimage_mono le_rfl)))] at h1
    convert h1 using 1
    rw [Module.Basis.det_apply, Module.Basis.det_apply]
    refine (RingHom.map_det (f.appLE U' _ hT).hom _).trans ?_
    congr 1
    ext i j
    refine Eq.trans (hc.pullback_basis_repr f le_rfl hT (v j) i).symm ?_
    rw [Module.Basis.toMatrix_apply]
    congr 2
    exact (QCoh.pullbackSections_res f Q hT hle _).trans (QCoh.res_pullbackSections f Q _ _ _).symm
  have hb := Y.basicOpen_of_isUnit hu
  rw [Scheme.basicOpen_appLE] at hb
  have hy' : y ∈ V ⊓ f ⁻¹ᵁ U' := ⟨hy, hx⟩
  rw [← hb] at hy'
  refine ⟨X.basicOpen ((hc.basis le_rfl).det v), (X.basicOpen_le _).trans hle, hy'.2, fun T hT => ?_⟩
  simp only [Twist.resM_resM]
  rw [Ker.bijective_iff_isUnit_det (hc.basis ((hT.trans (X.basicOpen_le _)).trans le_rfl))]
  have h2 := hc.resG_det le_rfl (hT.trans (X.basicOpen_le _)) v
  simp only [hv, Twist.resM_resM] at h2
  rw [← h2, ← LB.resG_resG (X.basicOpen_le _) hT]
  exact (X.toRingedSpace.isUnit_res_basicOpen _).map _
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.QuotientFrameFromPermutation
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.Twist (resM)

private theorem UpperTheory.exists_basis_subfamily_local {R M ι : Type} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] {r : ℕ} (c : Module.Basis (Fin r) R M) (v : ι → M)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    ∃ t : Fin r → ι, Function.Injective t ∧
      Function.Bijective (Fintype.linearCombination R fun k => v (t k)) := by
  have := Module.Free.of_basis c
  have := Module.Finite.of_basis c
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat (R := R) v hv
  let ε := c.indexEquiv b
  refine ⟨fun k => a (ε k), fun i j h => ?_, ?_⟩
  · apply ε.injective
    apply b.injective
    rw [hb, hb]
    exact congrArg v h
  · rw [Function.Bijective, ← linearIndependent_iff_injective_fintypeLinearCombination,
      ← LinearMap.range_eq_top, Fintype.range_linearCombination]
    have e : (fun k => v (a (ε k))) = b.reindex ε.symm := by
      funext k
      simp [hb]
    rw [e]
    exact ⟨(b.reindex ε.symm).linearIndependent, (b.reindex ε.symm).span_eq⟩

theorem UpperTheory.quotient_frame_from_permutation :
    ∀ (X : Scheme.{0}) (E Q : X.Modules) (p : E ⟶ Q) (m r : ℕ) (U : X.Opens) (e : Fin m ⊕ Fin r → Γ(E, U)) (x : X),
        Epi p → IsFrame e → IsVB Q r → x ∈ U →
        ∃ (σ : Equiv.Perm (Fin m ⊕ Fin r)) (W : X.Opens) (hW : W ≤ U), x ∈ W ∧
          IsFrame fun k => resM Q hW (p.app U (e (σ (Sum.inr k)))) := by
  intro X E Q p m r U e x hp he hQ hx
  obtain ⟨V, c, -, hxV, hle, hc⟩ := hQ.exists_affine hx
  have hspan : Submodule.span (X.presheaf.stalk x) (Set.range fun i =>
      (Q.presheaf.germ U x hx (p.app U (e i)) : (Q.presheaf.stalk x :))) = ⊤ := by
    have h1 := (he.stalkBasis x hx).span_eq
    have h2 := congrArg (Submodule.map (QCoh.stalkLinear p x)) h1
    rw [Submodule.map_span, Submodule.map_top,
      LinearMap.range_eq_top.2 (QCoh.stalkLinear_surjective p x), ← Set.range_comp] at h2
    have h3 : (⇑(QCoh.stalkLinear p x) ∘ ⇑(he.stalkBasis x hx)) = fun i =>
        (Q.presheaf.germ U x hx (p.app U (e i)) : (Q.presheaf.stalk x :)) := by
      funext i
      rw [Function.comp_apply, he.stalkBasis_apply, QCoh.stalkLinear_germ]
    rw [h3] at h2
    exact h2
  obtain ⟨t, ht, hb⟩ := UpperTheory.exists_basis_subfamily_local (hc.stalkBasis x hxV) _ hspan
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (f := (Sum.inr : Fin r → Fin m ⊕ Fin r))
    (g := t) Sum.inr_injective ht
  obtain ⟨W, hW, hxW, hv⟩ := Ker.exists_isFrame_of_bijective_stalk hc
    (fun k => resM Q hle (p.app U (e (t k)))) hxV (by
      simp only [Twist.germ_resM]
      exact hb)
  refine ⟨σ, W, hW.trans hle, hxW, ?_⟩
  simp only [Twist.resM_resM] at hv
  simp only [hσ]
  exact hv
end

