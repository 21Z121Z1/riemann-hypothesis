import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0421
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ImgTransInlE
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma uni_empty_eq {α β : Type} [LinearOrder α] [LinearOrder β] (L : Finset α) :
    uni L (∅ : Finset β) = L.map (inlE : α ↪o α ⊕ₗ β).toEmbedding := by
  ext z
  simp only [uni, inlE, Finset.disjSum_empty, Finset.map_map, Finset.mem_map]
  simp

private lemma lft_uni' {α β : Type} [LinearOrder α] [LinearOrder β] (I : Finset α) (J : Finset β) :
    lft (uni I J) = I := by
  ext t
  simp [lft, uni]

private lemma rgt_uni' {α β : Type} [LinearOrder α] [LinearOrder β] (I : Finset α) (J : Finset β) :
    rgt (uni I J) = J := by
  ext t
  simp [rgt, uni]

private lemma img_trans_inlE {d : ℕ} {α β : Type} [LinearOrder α] [LinearOrder β] (e : Fin d ↪o α) :
    img (e.trans (inlE : α ↪o α ⊕ₗ β)) = uni (img e) (∅ : Finset β) := by
  rw [uni_empty_eq]
  ext t
  simp [img]

private lemma img_card {d : ℕ} {α : Type} [LinearOrder α] (e : Fin d ↪o α) : (img e).card = d := by
  simp [img]

theorem UpperTheory.Gal.productCup_of_system.zEx_of :
    ZCol → ColZ → CechKoszulSystemCocycleGluing → KoszulBoundaryOfComponentMemIdeal → KSub → RS → ActsLin → SysOk → GoodZ → ThMuLat → ZEx := by
  intro hZCol hColZ hSysL2 hK2 hKSub hRS hActsLin hSysOk hGoodZ hThMu
  intro F K _ _ _ _ _ _ d x hcov τ htop a ha κ _ _ n z hz
  have hGood : (sysZ K x a).Good := (hGoodZ F K d x hcov a).1
  have hAdm : (sysZ K x a).admitted (app n11 n) (app (sysZ K x a).mu z) := by
    intro i j l
    obtain ⟨l, rfl⟩ : ∃ l', toLex l' = l := ⟨ofLex l, rfl⟩
    cases l with
    | inl m => exact (hThMu d _ _ (sysZ K x a) hGood).1 i j m
    | inr k => exact hz.adm i j k
  have gen : ∀ (T : Sys d (K ⊗[ℂ] K) (DR ℂ K ⊗[ℂ] DR ℂ K)) (i j : Fin (d + 1)),
      (fun l => T.r (app n11 n) (app T.mu z) i j (((dj j).trans (inlE (κ := κ))) l)) =
        fun l => T.r n11 T.mu i j (dj j l) := fun T i j => rfl
  have hOk := hSysOk d _ _ (sysZ K x a) _ (app n11 n) (app (sysZ K x a).mu z) hGood hAdm
  have key : ∀ (I J : Finset (Fin (d + 1))) (i j : Fin (d + 1)), i ∈ I → j ∈ J →
      ∀ D ∈ ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J).Z d,
      Acts (F := F) K τ a (D (uni (img (dj j)) ∅)) 0 →
      D ∈ ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J).B d := by
    intro I J i j hi hj D hD hA
    have hI : I.Nonempty := ⟨i, hi⟩
    have hJ : J.Nonempty := ⟨j, hj⟩
    obtain ⟨hr, hcol⟩ := hOk.2.1 I J i hi j hj
    rw [hcol] at hD ⊢
    have hR := hRS _ _ (sysZ K x a).act _ ((sysZ K x a).M I J) ((sysZ K x a).u (app n11 n) i j)
      ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (app (sysZ K x a).mu z) (fun l => rfl) d D
    rw [hR.2.2.1]
    rw [hR.2.1] at hD
    have hCZ := hColZ F K d x hcov τ htop a ha I J i hi j hj
    refine hK2 _ _ (sysZ K x a).act _ ((sysZ K x a).R I J) ((sysZ K x a).M I J) _ d ((dj j).trans inlE)
      (hGood.stab I J hI hJ) hr (by rw [gen]; exact hCZ.1) _ hD ?_
    rw [img_trans_inlE, gen]
    refine hCZ.2 _ ?_ ?_
    · have hC := (Submodule.mem_inf.1 hD).1
      simp only [kos, acx] at hC
      have h1 := (Submodule.mem_pi.1 hC) (uni (img (dj j)) ∅) (Set.mem_univ _)
      have hcard : (uni (img (dj j)) (∅ : Finset κ)).card = d := by
        rw [← img_trans_inlE, img_card]
      rw [hcard, if_pos rfl] at h1
      exact h1
    · have h2 := fun s => (hActsLin F K d x hcov τ htop a).2.1 _ 0 s hA
      simp only [mul_zero] at h2
      exact h2 _
  have hKE : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty →
      KE ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) I J) d := by
    intro I J hI hJ
    obtain ⟨i, hi⟩ := hI
    obtain ⟨j, hj⟩ := hJ
    obtain ⟨hr, hcol⟩ := hOk.2.1 I J i hi j hj
    rw [hcol]
    have hks := (hKSub _ _ (sysZ K x a).act _ ((sysZ K x a).R I J) ((sysZ K x a).M I J)
      ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (hGood.stab I J ⟨i, hi⟩ ⟨j, hj⟩) hr).1 d
      ((dj j).trans inlE) (by rw [gen]; exact (hColZ F K d x hcov τ htop a ha I J i hi j hj).1)
    intro m hm c hc
    have hR := hRS _ _ (sysZ K x a).act _ ((sysZ K x a).M I J) ((sysZ K x a).u (app n11 n) i j)
      ((sysZ K x a).r (app n11 n) (app (sysZ K x a).mu z) i j) (app (sysZ K x a).mu z) (fun l => rfl) m c
    rw [hR.2.2.1]
    exact hks m hm (hR.2.1.1 hc)
  have hc0 := fun i j => hZCol F K d x hcov τ htop a ha κ n z hz i j
  choose c0 hc0Z hc0A using hc0
  have hAct := (hActsLin F K d x hcov τ htop a).1
  obtain ⟨c, hcZ, hcol⟩ := hSysL2 d _ _ (sysZ K x a) _ (app n11 n) (app (sysZ K x a).mu z) hGood hAdm hKE c0 hc0Z
    (fun i i' j => by
      apply key {i, i'} {j} i j (by simp) (by simp)
      · exact Submodule.sub_mem _
          (hOk.2.2 {i} {i, i'} {j} {j} (by simp) (by simp) (by simp) le_rfl d (hc0Z i j))
          (hOk.2.2 {i'} {i, i'} {j} {j} (by simp) (by simp) (by simp) le_rfl d (hc0Z i' j))
      · have h3 := (hAct _ _ _ _ (hc0A i j _ (img_card (dj j))) (hc0A i' j _ (img_card (dj j)))).2
        rw [sub_self] at h3
        exact h3)
    (fun i j j' => by
      apply key {i} {j, j'} i j (by simp) (by simp)
      · exact Submodule.sub_mem _
          (hOk.2.2 {i} {i} {j} {j, j'} (by simp) (by simp) le_rfl (by simp) d (hc0Z i j))
          (hOk.2.2 {i} {i} {j'} {j, j'} (by simp) (by simp) le_rfl (by simp) d (hc0Z i j'))
      · have h3 := (hAct _ _ _ _ (hc0A i j _ (img_card (dj j))) (hc0A i j' _ (img_card (dj j)))).2
        rw [sub_self] at h3
        exact h3)
  refine ⟨c, hcZ, ?_⟩
  intro i j L hLc
  have e : resK inlE c (uni (uni {i} {j}) L) = c0 i j (uni L ∅) := by
    rw [← hcol i j]
    simp only [resK, col, lft_uni', rgt_uni', uni_empty_eq]
  rw [e]
  exact hc0A i j L hLc
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KoszulActionInclusion
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system.KoszulColumns

section Gen
variable {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)

private lemma sm_image {ι : Type} (M : Submodule ℂ E) (f : ι → S) (A : Set ι) :
    sm act M (f '' A) = ⨆ k ∈ A, M.map (act (f k)) := by
  exact iSup_image (f := f) (g := fun r => M.map (act r))

private lemma sm_range {ι : Type} (M : Submodule ℂ E) (f : ι → S) :
    sm act M (Set.range f) = ⨆ k, M.map (act (f k)) := by
  exact iSup_range (f := f) (g := fun r => M.map (act r))

end Gen

section Sysx
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)

private lemma r_formula (i j a : Fin (d + 1)) :
    T.r n11 T.mu i j (toLex (a, j)) =
      ((T.X a * (T.X i)⁻¹ : Sˣ) : S) - ((T.X j * (T.X i)⁻¹ : Sˣ) : S) * ((T.Y a * (T.Y j)⁻¹ : Sˣ) : S) := by
  have h : (T.Y j : S) * (((T.Y j)⁻¹ : Sˣ) : S) = 1 := Units.mul_inv _
  simp only [Sys.r, Sys.u, n11, Sys.mu, pow_one, mul_inv, Units.val_mul, ofLex_toLex]
  linear_combination ((T.X a : S) * (((T.X i)⁻¹ : Sˣ) : S)) * h

end Sysx

section Inst
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

variable (F K) in
private def i0 : F ⊗[ℂ] F →ₐ[ℂ] F ⊗[ℂ] K :=
  Algebra.TensorProduct.map (AlgHom.id ℂ F) (IsScalarTower.toAlgHom ℂ F K)

private lemma koszulAction_inclusion (a : ℕ) (s : F ⊗[ℂ] F) :
    (sysP K x a).act (i0 F K s) = actF F F (DR ℂ K) s := by
  have : ((sysP K x a).act).comp (i0 F K) = actF F F (DR ℂ K) := by
    apply Algebra.TensorProduct.ext'
    intro p q
    apply TensorProduct.ext'
    intro u w
    simp [sysP, i0, actF, Module.endTensorEndAlgHom_apply]
  exact DFunLike.congr_fun this s

private lemma ctrF_eq (ψ : F →ₗ[F] F) (m : F ⊗[ℂ] DR ℂ K) :
    ctrF (DR ℂ K) ψ m = ψ 1 • mulP F K m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | tmul f w =>
    have h1 : ψ f = f * ψ 1 := by
      have := ψ.map_smul f (1 : F)
      simpa using this
    simp only [ctrF, mulP, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      AlgHom.toLinearMap_apply, Algebra.lsmul_coe, Algebra.linearMap_apply, LinearMap.restrictScalars_apply]
    rw [h1, algebraMap_smul, smul_smul, mul_comm]

end Inst

section Sysy
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)

private lemma r_mem (hg : T.Good) {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)
    (a : Fin (d + 1)) : T.r n11 T.mu i j (toLex (a, j)) ∈ T.R I J := by
  rw [r_formula]
  exact sub_mem (hg.memX I J ⟨j, hj⟩ i hi a)
    (mul_mem (hg.memX I J ⟨j, hj⟩ i hi j) (hg.memY I J ⟨i, hi⟩ j hj a))

private lemma r_mul_v (i j a : Fin (d + 1)) :
    T.r n11 T.mu i j (toLex (a, j)) * ((T.X i * (T.X j)⁻¹ : Sˣ) : S) = T.r n11 T.mu j j (toLex (a, j)) := by
  have h : (T.X i : S) * (((T.X i)⁻¹ : Sˣ) : S) = 1 := Units.mul_inv _
  rw [r_formula, r_formula]
  simp only [Units.val_mul]
  linear_combination ((T.X a : S) * (((T.X j)⁻¹ : Sˣ) : S) - (T.X j : S) * (((T.X j)⁻¹ : Sˣ) : S) *
    ((T.Y a : S) * (((T.Y j)⁻¹ : Sˣ) : S))) * h

private lemma koszulEntry_diagonal (i j : Fin (d + 1)) :
    T.r n11 T.mu i j (toLex (i, j)) =
      1 - ((T.X j * (T.X i)⁻¹ : Sˣ) : S) * ((T.Y i * (T.Y j)⁻¹ : Sˣ) : S) := by
  rw [r_formula]
  simp

end Sysy

section Main
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

private lemma r_jj (a : ℕ) (j : Fin (d + 1)) (l : Fin d) :
    (sysP K x a).r n11 (sysP K x a).mu j j (dj j l) = i0 F K (f0 x j l) := by
  have h : (dj j l) = toLex (j.succAbove l, j) := rfl
  rw [h, r_formula]
  simp [sysP, i0, f0, div_eq_mul_inv]

private lemma diag_case (hR : RegLat) (hO : LatOm) (hA : LatA) (hK : K1) (hc : IsFinCover ℂ K (xv x)) (a : ℕ)
    (hg : (sysP K x a).Good) (I J : Finset (Fin (d + 1))) (j : Fin (d + 1)) (hjI : j ∈ I) (hjJ : j ∈ J) :
    KE (kos (sysP K x a).act ((sysP K x a).M I J) fun l => (sysP K x a).r n11 (sysP K x a).mu j j (dj j l)) d ∧
    ∀ m ∈ (sysP K x a).M I J, mulP F K m = 0 →
      m ∈ sm (sysP K x a).act ((sysP K x a).M I J) (Set.range fun l => (sysP K x a).r n11 (sysP K x a).mu j j (dj j l)) := by
  have hL1 := (hA F d x hc.pd I j hjI).1
  have hL2 := (hO F K d x hc a J ⟨j, hjJ⟩).1
  obtain ⟨hreg, hker⟩ := hR F d x hc.pd F (DR ℂ K) I J _ _ hL1 hL2 j hjI hjJ
  have hact : ∀ l, (sysP K x a).act ((sysP K x a).r n11 (sysP K x a).mu j j (dj j l)) = actF F F (DR ℂ K) (f0 x j l) := by
    intro l
    rw [r_jj, koszulAction_inclusion]
  have e : ∀ A : Set (Fin d), sm (sysP K x a).act ((sysP K x a).M I J)
      ((fun l => (sysP K x a).r n11 (sysP K x a).mu j j (dj j l)) '' A) =
      sm (actF F F (DR ℂ K)) ((sysP K x a).M I J) (f0 x j '' A) := by
    intro A
    rw [sm_image, sm_image]
    simp only [hact]
  constructor
  · refine hK _ _ (sysP K x a).act (Fin d) ((sysP K x a).R I J) _ _ d
      (fun l => (sysP K x a).r n11 (sysP K x a).mu j j (dj j l)) (hg.stab I J ⟨j, hjI⟩ ⟨j, hjJ⟩) ?_ ?_ ?_
    · exact fun l => r_mem _ hg hjI hjJ _
    · intro k m hm h
      rw [e] at h ⊢
      rw [hact] at h
      exact hreg k m hm h
    · intro k
      refine ⟨Pi.single k 1, fun l => ?_, ?_⟩
      · by_cases h : l = k
        · subst h; simpa using one_mem _
        · simpa [Pi.single_apply, h] using zero_mem _
      · simp [Pi.single_apply]
  · intro m hm h0
    have e2 : sm (sysP K x a).act ((sysP K x a).M I J)
        (Set.range fun l => (sysP K x a).r n11 (sysP K x a).mu j j (dj j l)) =
        sm (actF F F (DR ℂ K)) ((sysP K x a).M I J) (Set.range (f0 x j)) := by
      rw [sm_range, sm_range]
      simp only [hact]
    rw [e2]
    exact hker m hm fun ψ => by rw [ctrF_eq, h0, smul_zero]

private lemma loc_step (hA : LatA) (hc : IsFinCover ℂ K (xv x)) (a : ℕ) (hg : (sysP K x a).Good)
    (I J : Finset (Fin (d + 1))) (i j : Fin (d + 1)) (hi : i ∈ I) (hj : j ∈ J) :
    ∀ m ∈ (sysP K x a).M (insert j I) J,
      ∃ N : ℕ, (sysP K x a).act ((((sysP K x a).X j * ((sysP K x a).X i)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) ^ N) m ∈
        (sysP K x a).M I J := by
  set aa : F ⊗[ℂ] K := (((sysP K x a).X j * ((sysP K x a).X i)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) with haa
  have hmem : aa ∈ (sysP K x a).R I J := hg.memX I J ⟨j, hj⟩ i hi j
  have hst := hg.stab I J ⟨i, hi⟩ ⟨j, hj⟩
  have hup : ∀ (N k : ℕ) (m : F ⊗[ℂ] DR ℂ K), (sysP K x a).act (aa ^ N) m ∈ (sysP K x a).M I J →
      (sysP K x a).act (aa ^ (N + k)) m ∈ (sysP K x a).M I J := by
    intro N k m h
    rw [add_comm, pow_add, map_mul]
    exact hst _ (pow_mem hmem k) _ h
  have hform : aa = ((x j : F) / x i) ⊗ₜ[ℂ] (1 : K) := by
    simp [haa, sysP, div_eq_mul_inv]
  let P : Submodule ℂ (F ⊗[ℂ] DR ℂ K) :=
    { carrier := {m | ∃ N : ℕ, (sysP K x a).act (aa ^ N) m ∈ (sysP K x a).M I J}
      add_mem' := by
        rintro m m' ⟨N, h⟩ ⟨N', h'⟩
        refine ⟨N + N', ?_⟩
        rw [map_add]
        refine add_mem (hup N N' m h) ?_
        rw [add_comm]
        exact hup N' N m' h'
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c m ⟨N, h⟩
        exact ⟨N, by rw [map_smul]; exact Submodule.smul_mem _ c h⟩ }
  have hle : (sysP K x a).M (insert j I) J ≤ P := by
    refine Submodule.map₂_le.2 fun y hy w hw => ?_
    obtain ⟨N, hN⟩ := (hA F d x hc.pd I i hi).2.2 j y hy
    refine ⟨N, ?_⟩
    have : (sysP K x a).act (aa ^ N) (y ⊗ₜ[ℂ] w) = ((((x j : F) / x i) ^ N * y) ⊗ₜ[ℂ] w) := by
      rw [hform, Algebra.TensorProduct.tmul_pow, one_pow]
      simp [sysP, Module.endTensorEndAlgHom_apply]
      rw [← map_pow]
      rfl
    change (sysP K x a).act (aa ^ N) (y ⊗ₜ[ℂ] w) ∈ _
    rw [this]
    exact Submodule.apply_mem_map₂ _ hN hw
  exact fun m hm => hle hm

end Main

end UpperTheory.Gal.productCup_of_system.KoszulColumns

theorem UpperTheory.Gal.productCup_of_system.colP_of :
    RegLat → LatOm → LatA → K1 → LocD → GoodZ → ColP := by
  intro hR hO hA hK hL hG F K _ _ _ _ _ _ d x hc a I J i hi j hj
  have hg : (sysP K x a).Good := (hG F K d x hc a).2.1
  by_cases hij : i = j
  · subst hij
    exact KoszulColumns.diag_case x hR hO hA hK hc a hg I J i hi hj
  · obtain ⟨l0, hl0⟩ := Fin.exists_succAbove_eq hij
    have Ine : I.Nonempty := ⟨i, hi⟩
    have Jne : J.Nonempty := ⟨j, hj⟩
    have hjI' : j ∈ insert j I := Finset.mem_insert_self j I
    have hiI' : i ∈ insert j I := Finset.mem_insert_of_mem hi
    have Ine' : (insert j I).Nonempty := ⟨j, hjI'⟩
    have D := KoszulColumns.diag_case x hR hO hA hK hc a hg (insert j I) J j hjI' hj
    have hle : (sysP K x a).M I J ≤ (sysP K x a).M (insert j I) J :=
      hg.monoM I (insert j I) J J Ine Jne (Finset.subset_insert j I) subset_rfl
    have hst' := hg.stab (insert j I) J Ine' Jne
    have LD := hL _ _ (sysP K x a).act (Fin d) ((sysP K x a).R I J) ((sysP K x a).M I J) ((sysP K x a).M (insert j I) J)
      (fun l => (sysP K x a).r n11 (sysP K x a).mu i j (dj j l)) ((sysP K x a).X i * ((sysP K x a).X j)⁻¹)
      (((sysP K x a).X j * ((sysP K x a).X i)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K)
      (((sysP K x a).Y i * ((sysP K x a).Y j)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) l0 d
      (hg.stab I J Ine Jne) (fun l => KoszulColumns.r_mem _ hg hi hj _) (hg.memX I J Jne i hi j) (hg.memY I J Ine j hj i)
      (by
        have h : dj j l0 = toLex (i, j) := by rw [← hl0]; rfl
        simp only [h]
        exact KoszulColumns.koszulEntry_diagonal _ i j)
      hle (KoszulColumns.loc_step x hA hc a hg I J i j hi hj)
      (fun m hm => ⟨hst' _ (hg.memX _ J Jne j hjI' i) m hm, by
        have : (((sysP K x a).X i * ((sysP K x a).X j)⁻¹)⁻¹ : (F ⊗[ℂ] K)ˣ) = (sysP K x a).X j * ((sysP K x a).X i)⁻¹ := by
          simp [mul_comm]
        rw [this]
        exact hst' _ (hg.memX _ J Jne i hiI' j) m hm⟩)
    have hrv : (fun l => (sysP K x a).r n11 (sysP K x a).mu i j (dj j l) *
        (((sysP K x a).X i * ((sysP K x a).X j)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K)) =
        fun l => (sysP K x a).r n11 (sysP K x a).mu j j (dj j l) := by
      funext l
      exact KoszulColumns.r_mul_v _ i j _
    rw [hrv] at LD
    exact ⟨LD.1 D.1, fun m hm h0 => LD.2 m hm (D.2 m (hle hm) h0)⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PDualForm
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma perfectPairing_surjective {F Q P : Type*} [Field F] [AddCommGroup Q] [Module F Q] [AddCommGroup P] [Module F P]
    [FiniteDimensional F Q] [FiniteDimensional F P] (hr : Module.finrank F Q = Module.finrank F P)
    (B : Q →ₗ[F] P →ₗ[F] F) (hB : ∀ w, (∀ y, B w y = 0) → w = 0) :
    Function.Surjective B ∧ Function.Surjective B.flip := by
  have hinj : Function.Injective B :=
    (injective_iff_map_eq_zero B).2 fun w hw => hB w fun y => by simp [hw]
  have hs : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [show Module.finrank F (P →ₗ[F] F) = Module.finrank F P from Subspace.dual_finrank_eq, hr])).1 hinj
  refine ⟨hs, ?_⟩
  have hinj' : Function.Injective B.flip := by
    refine (injective_iff_map_eq_zero B.flip).2 fun y hy => ?_
    refine (Module.forall_dual_apply_eq_zero_iff F y).1 fun f => ?_
    obtain ⟨w, rfl⟩ := hs f
    exact LinearMap.congr_fun hy w
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [show Module.finrank F (Q →ₗ[F] F) = Module.finrank F Q from Subspace.dual_finrank_eq, hr])).1 hinj'

theorem UpperTheory.Gal.productCup_of_system.dualForm_of :
    DualForm := by
  intro F K _ _ _ _ _ _ d x hc τ ht a ha ψ
  obtain ⟨hinj, hrk, hfdP⟩ := GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms ℂ F K d (xv x) hc τ ht (d - a) a (by omega)
  obtain ⟨-, -, hfdQ⟩ := GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms ℂ F K d (xv x) hc τ ht a (d - a) (by omega)
  haveI : FiniteDimensional F K := hc.fin
  haveI : FiniteDimensional F (⋀[K]^(d - a) Ω[K⁄ℂ]) := Module.Finite.trans K _
  haveI : FiniteDimensional F (⋀[K]^a Ω[K⁄ℂ]) := Module.Finite.trans K _
  let T : DR ℂ K →ₗ[F] F := (Algebra.trace F K) ∘ₗ (τ.restrictScalars F)
  let B : (⋀[K]^a Ω[K⁄ℂ]) →ₗ[F] (⋀[K]^(d - a) Ω[K⁄ℂ]) →ₗ[F] F :=
    LinearMap.mk₂ F (fun w y => T ((y : DR ℂ K) * (w : DR ℂ K)))
      (fun w w' y => by simp [mul_add])
      (fun c w y => by simp [mul_smul_comm])
      (fun w y y' => by simp [add_mul])
      (fun c w y => by simp [smul_mul_assoc])
  have hr : Module.finrank F (⋀[K]^a Ω[K⁄ℂ]) = Module.finrank F (⋀[K]^(d - a) Ω[K⁄ℂ]) := by
    rw [← Module.finrank_mul_finrank F K (⋀[K]^a Ω[K⁄ℂ]),
      ← Module.finrank_mul_finrank F K (⋀[K]^(d - a) Ω[K⁄ℂ]), hrk]
  obtain ⟨hs, hs'⟩ := perfectPairing_surjective hr B (fun w hw => Subtype.ext (hinj w.1 w.2 fun y hy => hw ⟨y, hy⟩))
  constructor
  · obtain ⟨w, hw⟩ := hs (ψ ∘ₗ (Submodule.subtype _).restrictScalars F)
    exact ⟨w.1, w.2, fun y hy => (LinearMap.congr_fun hw ⟨y, hy⟩).symm⟩
  · obtain ⟨w, hw⟩ := hs' (ψ ∘ₗ (Submodule.subtype _).restrictScalars F)
    exact ⟨w.1, w.2, fun y hy => (LinearMap.congr_fun hw ⟨y, hy⟩).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PrBOf
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.prB_of :
    GoodZ → PrB := by
  intro hG F K _ _ _ _ _ _ d x h τ hτ ρ hρ a q had hqd e he y hy
  have mono : ∀ r : ℕ, ∀ s t : Finset (Fin (d + 1)), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) r ≤ omB ℂ K (rB ℂ K (xv x) t) r :=
    fun r => (hG F K d x h r).2.2
  have hvan : ∀ i, (Finset.univ.erase i).Nonempty →
      ∀ u ∈ omB ℂ K (rB ℂ K (xv x) (Finset.univ.erase i)) (d - a),
      ∀ v ∈ omB ℂ K (rB ℂ K (xv x) (Finset.univ.erase i)) a,
      (LinearMap.mul ℂ (DR ℂ K)).compr₂ (trF ℂ τ ρ) u v = 0 := by
    intro i hi u hu v hv
    have hvq : v ∈ ⋀[K]^a Ω[K⁄ℂ] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties ℂ K _ a 0).2.1 v hv).2.2.1
    have hmem := (GlobalTheory.T.twistedDual_regularForms_finiteCover ℂ F K d (xv x) h τ hτ (Finset.univ.erase i) hi (d - a) a
      (by omega) v hvq).2 hv u hu
    exact GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) h.pd ρ hρ i _ hi (Finset.notMem_erase i _) _ hmem
  obtain ⟨ε, hε⟩ := GlobalTheory.T.cechDifferential_adjoint_cupProductPairing ℂ d _ _ (fun I => omB ℂ K (rB ℂ K (xv x) I) (d - a))
    (fun I => omB ℂ K (rB ℂ K (xv x) I) a) ((LinearMap.mul ℂ (DR ℂ K)).compr₂ (trF ℂ τ ρ))
    (mono _) (mono _) hvan ((d : ℤ) - (q : ℕ))
  obtain ⟨y', hy', rfl⟩ := hy
  have key := hε e he.1 y' (by
    have e1 : (d : ℤ) - ((d : ℤ) - (q : ℕ)) - 1 = (q : ℤ) - 1 := by ring
    rw [e1]
    exact hy')
  have h0 : (cech fun I => omB ℂ K (rB ℂ K (xv x) I) (d - a)).D e = 0 := he.2
  rw [h0, map_zero, LinearMap.zero_apply] at key
  exact (smul_eq_zero_iff_eq ε).1 key.symm
end

