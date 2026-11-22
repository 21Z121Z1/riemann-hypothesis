import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.LinearFormDegree.InvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmLatticeDataUnfoldingSignatureOneZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.CMRankOne

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_pure_of_data (Y : FD.Data E r) (x : FD.Frame Y.Ψ r) (hx : x ∈ Y.dom) (lam : Fin r → Fin r → E)
    (ho : ∀ j k' : Fin r, (j : ℕ) < Y.p0 → Y.p0 ≤ (k' : ℕ) → FD.herm Y.Gm (lam j) (lam k') = 0)
    (hsp : ∀ τ : Y.Ψ, Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.col (FD.mat x τ) (Fin.castLE Y.p0_le a)) =
      Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.Data.emb τ.1 (lam (Fin.castLE Y.p0_le a))))
    (a : E) (j : Fin r) (τ : E →+* ℂ) (i : ℕ) :
    ((j : ℕ) < Y.p0 → τ ∈ Y.Ψ → perFr Y x (a • lam j) τ i = 0) ∧
      (Y.p0 ≤ (j : ℕ) → τ ∉ Y.Ψ → i < Y.p0 → perFr Y x (a • lam j) τ i = 0) := by
  refine ⟨fun hj hτ => ?_, fun hj hτ hi => ?_⟩
  · unfold perFr
    rw [dif_pos hτ]
    split_ifs with h
    · refine GlobalTheory.PurePer.inv_mulVec_eq_zero Y.p0_le _ (hx ⟨τ, hτ⟩).1 ?_ _ (by simp)
      rw [hsp ⟨τ, hτ⟩, GlobalTheory.PurePer.emb_smul']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    · rfl
  · unfold perFr
    rw [dif_neg hτ]
    split_ifs with h' h
    · have hm : FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨Y.p0 - 1 - i, h⟩ ∈
          Submodule.span ℂ (Set.range fun a : Fin Y.p0 =>
            FD.Data.emb (conjEmb τ) (lam (Fin.castLE Y.p0_le a))) := by
        have := hsp ⟨conjEmb τ, h'⟩
        simp only at this
        rw [← this]
        exact Submodule.subset_span ⟨⟨Y.p0 - 1 - i, by omega⟩, rfl⟩
      rw [GlobalTheory.PurePer.emb_smul', FD.hermC_smul_right]
      refine mul_eq_zero_of_right _ ?_
      generalize FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨Y.p0 - 1 - i, h⟩ = w at hm
      induction hm using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨k, rfl⟩ := hw
        rw [FD.hermC_emb, ho _ j (by simpa using k.isLt) hj, map_zero]
      | zero => exact FD.hermC_zero_left _ _ _
      | add a b _ _ ha hb => rw [FD.hermC_add_left, ha, hb, add_zero]
      | smul c a _ ha => rw [FD.hermC_smul_left, ha, mul_zero]
    · rfl
    · rfl

theorem exists_cmLat_rankOne (H : Host E) {p q : ℕ} (Y : FD.Data E r) (x₀ : Y.dom)
    (hr : 0 < r) (hrk : r = p + q) (hp0 : Y.p0 = q) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0)
    (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
    (φ : D.La ≃ₗ[𝓞 E] Y.Λ)
    (isom : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-Y.ξ0 * FD.herm Y.Gm (φ a : Fin r → E) (φ b)))
    (ix : Fin g → ℕ) (hix : ∀ j, ty j (H.rt : E) ≠ H.rt0 → ix j < q)
    (pm : ∀ a j, Pe a j = perFr Y x₀.1 (φ a : Fin r → E) (ty j) (ix j))
    (D₁ : Datum H) (hp1 : D₁.p = 1) (hq1 : D₁.q = 0)
    (lam : Fin r → Fin r → E) (hL : ∀ j, lam j ∈ Y.Λ) (hli : LinearIndependent E lam)
    (ho : ∀ j k' : Fin r, (j : ℕ) < Y.p0 → Y.p0 ≤ (k' : ℕ) → FD.herm Y.Gm (lam j) (lam k') = 0)
    (hsp : ∀ τ : Y.Ψ, Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.col (FD.mat x₀.1 τ) (Fin.castLE Y.p0_le a)) =
      Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.Data.emb τ.1 (lam (Fin.castLE Y.p0_le a)))) :
    Nonempty (CMLat hP p q) := by
  classical
  have hpure := perFr_pure_of_data Y x₀.1 x₀.2 lam ho hsp
  obtain ⟨G1, io, hioinj, -, -, hG1det, hEF1⟩ :=
    GlobalTheory.exists_herm_coord_of_datum E H D₁ Y.ξ0 Y.ξ0_im Y.ξ0_ne 1 (by omega)
  let lv : D₁.La →ₗ[𝓞 E] E := (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin 1 => E) 0) ∘ₗ io
  have hlv : ∀ x, lv x = io x 0 := fun x => rfl
  have hG0 : G1 0 0 ≠ 0 := by simpa [Matrix.det_unique] using hG1det
  have hform1 : ∀ x y, ((D₁.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (Y.ξ0 * G1 0 0 * lv x * FD.cc (lv y)) := by
    intro x y
    rw [hEF1]
    congr 1
    simp [FD.herm, hlv]
    ring
  have h1ne : (1 : Submodule (𝓞 E) E) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨1, Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero⟩

  obtain ⟨S, hS⟩ := D₁.fin.fg_top
  obtain ⟨N₀, hN₀, hc₀⟩ := GlobalTheory.LamT.CMBasis.exists_nsmul_mem (1 : Submodule (𝓞 E) E) h1ne (fun s : S => lv s)
  let lv0 : D₁.La →ₗ[𝓞 E] E := (N₀ : 𝓞 E) • lv
  have hlv0 : ∀ x, lv0 x = (N₀ : E) * lv x := fun x => by
    simp [lv0, Algebra.smul_def]
  have hlv01 : ∀ x, lv0 x ∈ (1 : Submodule (𝓞 E) E) := by
    have : (⊤ : Submodule (𝓞 E) D₁.La) ≤ (1 : Submodule (𝓞 E) E).comap lv0 := by
      rw [← hS, Submodule.span_le]
      intro s hs
      change lv0 s ∈ (1 : Submodule (𝓞 E) E)
      rw [hlv0]
      exact hc₀ ⟨s, hs⟩
    exact fun x => this Submodule.mem_top

  obtain ⟨M, hM, hcM⟩ := GlobalTheory.LamT.CMBasis.exists_nsmul_mem (1 : Submodule (𝓞 E) E) h1ne
    (fun i : Fin r => (N₀ : E) ^ 2 * FD.herm Y.Gm (lam i) (lam i) / G1 0 0)
  choose t ht using fun i => Submodule.mem_one.1 (hcM i)
  let lv' : D₁.La →ₗ[𝓞 E] E := (M : 𝓞 E) • lv0
  have hlv' : ∀ x, lv' x = ((N₀ * M : ℕ) : E) * lv x := fun x => by
    simp only [lv', LinearMap.smul_apply, Algebra.smul_def, hlv0]
    push_cast
    ring
  have hlv'1 : ∀ x, lv' x ∈ (1 : Submodule (𝓞 E) E) := fun x =>
    Submodule.smul_mem _ (M : 𝓞 E) (hlv01 x)
  have hmem : ∀ x j, lv' x • lam j ∈ Y.Λ := fun x j => by
    obtain ⟨u, hu⟩ := Submodule.mem_one.1 (hlv'1 x)
    rw [← hu, algebraMap_smul]
    exact Y.Λ.smul_mem u (hL j)
  let m : Fin r → D₁.La →ₗ[𝓞 E] Y.Λ := fun j =>
    { toFun := fun a => ⟨_, hmem a j⟩
      map_add' := fun a b => Subtype.ext (by simp [add_smul])
      map_smul' := fun c a => Subtype.ext (by simp [smul_assoc]) }
  let Dp : Bool → Datum H := fun b => match b with
    | true => D₁
    | false => oppDatum D₁
  let e : ∀ b, (Dp b).La ≃ₗ[𝓞 E] D₁.La := fun b => match b with
    | true => LinearEquiv.refl _ _
    | false => LinearEquiv.refl _ _
  let σ : Fin p ⊕ Fin q ≃ Fin r := (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))
  have hσl : ∀ j, q ≤ (σ (.inl j) : ℕ) := fun j => by simp [σ]
  have hσr : ∀ j, (σ (.inr j) : ℕ) < q := fun j => by simp [σ]
  let f : ∀ j : Fin p ⊕ Fin q, (Dp j.isLeft).La →ₗ[𝓞 E] D.La := fun j =>
    φ.symm.toLinearMap ∘ₗ m (σ j) ∘ₗ (e _).toLinearMap
  have hf : ∀ j a, (φ (f j a) : Fin r → E) = lv' (e _ a) • lam (σ j) := fun j a => by
    simp [f, m]
  let hh : Fin p ⊕ Fin q → 𝓞 E :=
    Sum.elim (fun j => -((M : 𝓞 E) * t (σ (.inl j)))) (fun j => (M : 𝓞 E) * t (σ (.inr j)))
  have hhl : ∀ j, ((hh (.inl j) : 𝓞 E) : E) =
      -(((N₀ * M : ℕ) : E) ^ 2 * FD.herm Y.Gm (lam (σ (.inl j))) (lam (σ (.inl j))) / G1 0 0) := by
    intro j
    show ((-((M : 𝓞 E) * t (σ (.inl j))) : 𝓞 E) : E) = _
    rw [RingOfIntegers.coe_eq_algebraMap, map_neg, map_mul, ht, map_natCast]
    push_cast
    ring
  have hhr : ∀ j, ((hh (.inr j) : 𝓞 E) : E) =
      ((N₀ * M : ℕ) : E) ^ 2 * FD.herm Y.Gm (lam (σ (.inr j))) (lam (σ (.inr j))) / G1 0 0 := by
    intro j
    show ((((M : 𝓞 E) * t (σ (.inr j))) : 𝓞 E) : E) = _
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul, ht, map_natCast]
    push_cast
    ring
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := fun τ => by
    refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
    rw [← map_pow, HostModel.coe_sq_eq_neg H.rt_sq, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  have h3 : ∀ (a b : E) (u : Fin r → E), FD.herm Y.Gm (a • u) (b • u) = a * FD.cc b * FD.herm Y.Gm u u :=
    fun a b u => by
      simp only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hccN : ∀ n : ℕ, FD.cc (n : E) = n := fun n => by simp [FD.cc]
  have hlvs : ∀ (c : 𝓞 E) x, lv (c • x) = (c : E) * lv x := fun c x => by
    rw [map_smul, Algebra.smul_def]
  refine ⟨⟨Dp, ⟨hp1, hq1⟩, ⟨hq1, hp1⟩, f, ?_, hh, ?_, ?_⟩⟩
  · rintro (j | j) a k hk
    · rw [pm, hf]
      have hk' : ty k (H.rt : E) ≠ H.rt0 := by simpa using hk
      exact (hpure _ _ _ _).2 (hp0 ▸ hσl j) (fun h => hk' ((hΨ _).1 h)) (hp0 ▸ hix k hk')
    · rw [pm, hf]
      have hk' : ty k (H.rt : E) ≠ -H.rt0 := by simpa using hk
      exact (hpure _ _ _ _).1 (hp0 ▸ hσr j) ((hΨ _).2 ((hsq _).resolve_right hk'))
  · rintro (j | j) a b
    · apply Int.cast_injective (α := ℚ)
      rw [isom, hf, hf]
      refine Eq.trans ?_ (hform1 (hh (.inl j) • a) b).symm
      erw [hlvs]
      congr 1
      change -Y.ξ0 * FD.herm Y.Gm (lv' a • lam (σ (.inl j))) (lv' b • lam (σ (.inl j))) = _
      rw [h3]
      erw [hlv' a, hlv' b]
      rw [hhl]
      simp only [FD.cc, map_mul, map_natCast]
      field_simp
    · apply Int.cast_injective (α := ℚ)
      rw [isom, hf, hf]
      refine Eq.trans ?_ (congrArg (fun z : ℚ => -z) (hform1 (hh (.inr j) • a) b)).symm |>.trans (by push_cast; rfl)
      erw [hlvs]
      rw [← map_neg]
      congr 1
      change -Y.ξ0 * FD.herm Y.Gm (lv' a • lam (σ (.inr j))) (lv' b • lam (σ (.inr j))) = _
      rw [h3]
      erw [hlv' a, hlv' b]
      rw [hhr]
      simp only [FD.cc, map_mul, map_natCast]
      field_simp
  · haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
    have hB : ∀ j, B j = lam j := fun j => by simp [B]
    let Nm : Submodule (𝓞 E) D.La := LinearMap.range (∑ j, f j ∘ₗ LinearMap.proj j)
    have hN : ∀ a, a ∈ Nm ↔ ∃ x : ∀ j : Fin p ⊕ Fin q, (Dp j.isLeft).La, a = ∑ j, f j (x j) := fun a => by
      simp only [Nm, LinearMap.mem_range, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      exact exists_congr fun _ => eq_comm
    have hnt : Nontrivial D₁.La :=
      Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D₁.rank, hp1, hq1]; exact one_pos)
    obtain ⟨a₀, ha₀⟩ := exists_ne (0 : D₁.La)
    have hR : LinearMap.range lv' ≠ ⊥ := by
      refine (Submodule.ne_bot_iff _).2 ⟨lv' a₀, ⟨a₀, rfl⟩, ?_⟩
      rw [hlv']
      refine mul_ne_zero (by exact_mod_cast (Nat.mul_pos hN₀ hM).ne') fun h0 => ha₀ (hioinj ?_)
      funext i
      rw [Subsingleton.elim i 0, map_zero]
      exact h0
    obtain ⟨S', hS'⟩ := D.fin.fg_top
    obtain ⟨n, hn, hc⟩ := GlobalTheory.LamT.CMBasis.exists_nsmul_mem (LinearMap.range lv') hR
      (fun i : S' × Fin r => B.repr (φ i.1 : Fin r → E) i.2)
    choose y hy using fun i : S' × Fin r => LinearMap.mem_range.1 (hc i)
    refine ⟨n, hn, fun a => (hN _).1 ?_⟩
    have : (⊤ : Submodule (𝓞 E) D.La) ≤ Nm.comap (n • LinearMap.id) := by
      rw [← hS', Submodule.span_le]
      intro a ha
      refine (hN _).2 ⟨fun j => (e _).symm (y (⟨a, ha⟩, σ j)), φ.injective (Subtype.ext ?_)⟩
      rw [map_sum, AddSubmonoidClass.coe_finsetSum]
      simp only [hf, LinearEquiv.apply_symm_apply, hy]
      rw [Equiv.sum_comp σ (fun j => ((n : E) * B.repr (φ a : Fin r → E) j) • lam j)]
      simp only [mul_smul, ← Finset.smul_sum, ← hB, B.sum_repr]
      simp [Nat.cast_smul_eq_nsmul]
    exact this Submodule.mem_top

theorem exists_cmLat_unfAt_rankOne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (r : ℕ) (U : Formalism.L2.Pj.Unf Xo c c.F.val.toRingHom r), Formalism.L2.Pj.IsUnf U → 0 < r → ∀ (D₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), D₁.p = 1 → D₁.q = 0 → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt U k x₀) (lam : Fin r → Fin r → E), (∀ j, lam j ∈ (U.X k).Λ) → LinearIndependent E lam → (∀ j k' : Fin r, (j : ℕ) < (U.X k).p0 → (U.X k).p0 ≤ (k' : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam k') = 0) → (∀ j : Fin r, (j : ℕ) < (U.X k).p0 → ∀ τ : (U.X k).Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam j))).re) → (∀ j : Fin r, (U.X k).p0 ≤ (j : ℕ) → ∀ τ : (U.X k).Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam j))).re < 0) → (∀ τ : (U.X k).Ψ, Submodule.span ℂ (Set.range fun a : Fin (U.X k).p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀.1 τ) (Fin.castLE (U.X k).p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin (U.X k).p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE (U.X k).p0_le a)))) → Nonempty (GlobalTheory.CM.CMLat W.per Dw.p Dw.q) := by
  intro E _ _ _ H Dw l Xo c r U hU hr D₁ hp1 hq1 k x₀ W lam hL hli ho _ _ hsp
  obtain ⟨h1, h2, -⟩ := hU
  refine exists_cmLat_rankOne H (U.X k) x₀ hr h1 (h2 k).1 (h2 k).2 _ W.per (W.φ k) (W.isom k)
    (fun j => (W.e j).2) (fun j hj => ?_) W.pm_eq D₁ hp1 hq1 lam hL hli ho hsp
  exact (W.e j).2.2.trans_eq (if_neg hj)

end GlobalTheory.LamT.CMRankOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantMeanSquareFormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenbergInvariant_meanSquare_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsCharAF D.host.F ψ → ∀ M : Submodule ℂ (WO S T → ℂ), (∀ f ∈ M, IsThetaFunO ψ S T f) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WO S T) (f g f' g' : M), (f' : WO S T → ℂ) = heisO ψ S T u f → (g' : WO S T → ℂ) = heisO ψ S T u g → B f' g' = B f g) ∧ ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WO S T → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (B f f).re := by
  first | exact @GlobalTheory.ThetaMeanSquareForm.exists_invariant_form | exact GlobalTheory.ThetaMeanSquareForm.exists_invariant_form | (intros; apply GlobalTheory.ThetaMeanSquareForm.exists_invariant_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntInv
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.IntInv

theorem exists_int_inv : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d : ℕ) (Θ : Fin d → MvPowerSeries (Fin d) C), (∀ a, MvIsInt v (Θ a)) → (∀ a, constantCoeff (Θ a) = 0) → (∀ a b, coeff (Finsupp.single b 1) (Θ a) = if a = b then 1 else 0) → ∃ Ψ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (Ψ a)) ∧ (∀ a, constantCoeff (Ψ a) = 0) ∧ (∀ a, subst Ψ (Θ a) = MvPowerSeries.X a) ∧ ∀ a, subst Θ (Ψ a) = MvPowerSeries.X a := by
  intro C _ _ v d Θ hint h0 h1
  set S := ReciprocityTheory.ChartRestriction.G.Sh.PTb.intRing v
  let Θ' : Fin d → MvPowerSeries (Fin d) S := fun a α => ⟨coeff α (Θ a), hint a α⟩
  have hΘ' : ∀ a, map S.subtype (Θ' a) = Θ a := fun a => by ext α; rfl
  have h0' : ∀ a, constantCoeff (Θ' a) = 0 := fun a => Subtype.ext (by
    change coeff 0 (Θ a) = 0
    rw [coeff_zero_eq_constantCoeff_apply]; exact h0 a)
  have h1' : ∀ a b, coeff (Finsupp.single b 1) (Θ' a) = (1 : Matrix (Fin d) (Fin d) S) a b := by
    intro a b
    apply Subtype.ext
    change coeff (Finsupp.single b 1) (Θ a) = _
    rw [h1 a b, Matrix.one_apply]
    split_ifs <;> rfl
  have hu : IsUnit (1 : Matrix (Fin d) (Fin d) S).det := by rw [Matrix.det_one]; exact isUnit_one
  obtain ⟨ψ, hψ0, hψΘ, hΘψ⟩ := ReciprocityTheory.ChartRestriction.G.LF.InvFun.exists_inv Θ' h0' 1 h1' hu
  have hsψ : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  have hsΘ : HasSubst Θ' := hasSubst_of_constantCoeff_zero h0'
  refine ⟨fun a => map S.subtype (ψ a), ?_, ?_, ?_, ?_⟩
  · intro a α
    rw [coeff_map]
    exact (coeff α (ψ a)).2
  · intro a
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hψ0 a]
    rfl
  · intro a
    have key := map_subst hsψ (h := S.subtype) (Θ' a)
    rw [hΘ', hψΘ a, map_X] at key
    exact key.symm
  · intro a
    have key := map_subst hsΘ (h := S.subtype) (ψ a)
    have e : (fun s => map S.subtype (Θ' s)) = Θ := funext hΘ'
    rw [e, hΘψ a, map_X] at key
    exact key.symm

end GlobalTheory.IntInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralModelOfGaloisStableTorsionStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralModel_of_galoisStable_torsion : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (F : IntermediateField ℚ ℂ) (ι : Type) [Fintype ι] (T : ι → ℂ), L.g₂ ∈ F → L.g₃ ∈ F → u ∈ F → Stable L F T → (∀ i, T i ∉ L.lattice ∧ (N : ℂ) * T i ∈ L.lattice) → V.valuation (Fintype.card ι : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  first | exact @GlobalTheory.CMModel.modelAt_of_stable_torsion | exact GlobalTheory.CMModel.modelAt_of_stable_torsion | (intros; apply GlobalTheory.CMModel.modelAt_of_stable_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem IsAmpleLB.eventually_isGenerated_tens_lbPow {X : Scheme.{0}} {A N : LB X} (hA : IsAmpleLB A)
    (hN : N.IsLB) : ∀ᶠ n : ℕ in atTop, IsGenerated (tens N (lbPow A n)) := by
  have := isFiniteQC_twist (F := GlobalTheory.structureModule X) hN
  refine (hA.eventually_isGloballyGenerated_twist (twist (GlobalTheory.structureModule X) N)).mono
    fun n hn => ?_
  have hP := isLB_lbPow hA.isLB n
  have hT := isLB_tens hN hP
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule X) hN hP hT
    (cls_tens hN hP hT)
  exact (isGloballyGenerated_toMod_iff hT).1 ((hn.of_epi e.hom).of_epi (unitTwistIso _).hom)

theorem IsAmpleLB.eventually_isAmpleLB_tens_lbPow_succ {X : Scheme.{0}} {A N : LB X}
    (hA : IsAmpleLB A) (hN : N.IsLB) : ∀ᶠ n : ℕ in atTop, IsAmpleLB (tens N (lbPow A (n + 1))) := by
  refine (hA.eventually_isGenerated_tens_lbPow hN).mono fun n hn => ?_
  have hP := isLB_lbPow hA.isLB n
  have hP' := isLB_lbPow hA.isLB (n + 1)
  have hT := isLB_tens hN hP'
  have hD := LB.isLB_div hT hA.isLB
  refine hA.tensor_isGenerated hn hT ((cls_eq_zero_iff (LB.isLB_div hD hn.isLB)).1 ?_)
  rw [cls_div hD hn.isLB, cls_div hT hA.isLB, cls_tens hN hP', cls_tens hN hP,
    cls_lbPow hA.isLB, cls_lbPow hA.isLB, succ_nsmul]
  abel

theorem exists_isAmpleLB_tens_lbPow : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ A N : LB X, IsAmpleLB A → N.IsLB → ∃ c : ℕ, 1 ≤ c ∧ IsAmpleLB (tens N (lbPow A c)) := by
  intro k _ _ X _ _ A N hA hN
  obtain ⟨n, hn⟩ := (hA.eventually_isAmpleLB_tens_lbPow_succ hN).exists
  exact ⟨n + 1, Nat.succ_pos n, hn⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsSemisimpleParameterGLFiniteField
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime]

theorem exists_labelsChar_of_pos (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) (θ : Tor p d →* ℂˣ) :
    ∃ x : Fbar p, LabelsChar L θ x := by
  have hp : 0 < p ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  haveI : NeZero (p ^ d - 1) := ⟨hp.ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have h0 : L.gen d ≠ 0 := hprim.ne_zero hp.ne'
  have hprimC : IsPrimitiveRoot (L.teich (L.gen d)) (p ^ d - 1) := by
    refine ⟨by rw [← map_pow, hprim.pow_eq_one, map_one], fun l hl => hprim.dvd_of_pow_eq_one l ?_⟩
    exact L.teich_inj _ _ (pow_ne_zero _ h0) one_ne_zero (by rw [map_pow, hl, map_one])
  let γ : Tor p d := ⟨Units.mk0 _ h0, by
    rw [mem_rootsOfUnity]
    exact Units.ext (by simpa using hprim.pow_eq_one)⟩
  have hγ : γ ^ (p ^ d - 1) = 1 := Subtype.ext ((mem_rootsOfUnity _ _).1 γ.2)
  obtain ⟨k, -, hk⟩ := hprimC.eq_pow_of_pow_eq_one (ξ := ((θ γ : ℂˣ) : ℂ))
    (by rw [← Units.val_pow_eq_pow_val, ← map_pow, hγ, map_one, Units.val_one])
  refine ⟨L.gen d ^ k, by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow], fun u => ?_⟩
  have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hu
  have hex : ∃ n : ℕ, ((u : (Fbar p)ˣ) : Fbar p) = L.gen d ^ n := ⟨n, hn.symm⟩
  unfold GlobalTheory.GLq.thetaOf
  rw [dif_pos hex]
  have e : u = γ ^ hex.choose := Subtype.ext (Units.ext (by simpa [γ] using hex.choose_spec))
  rw [map_pow, hk, ← Units.val_pow_eq_pow_val, ← map_pow, ← e]

theorem prod_frobenius_orbit_mem_lifts {d : ℕ} {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1) :
    (∏ i : Fin d, (X - C (x ^ p ^ (i : ℕ)))) ∈ Polynomial.lifts (algebraMap (ZMod p) (Fbar p)) := by
  have hxd : x ^ p ^ d = x := by
    have h1 : p ^ d = (p ^ d - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)).symm
    rw [h1, pow_succ, hx, one_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => (X - C (x ^ p ^ i) : (Fbar p)[X])) d]
  have hfix : (∏ i ∈ Finset.range d, (X - C (x ^ p ^ i) : (Fbar p)[X])).map (frobenius (Fbar p) p) =
      ∏ i ∈ Finset.range d, (X - C (x ^ p ^ i)) := by
    have h1 := Finset.prod_range_succ (fun i => (X - C (x ^ p ^ i) : (Fbar p)[X])) d
    rw [Finset.prod_range_succ', hxd, pow_zero, pow_one] at h1
    rw [Polynomial.map_prod, ← mul_right_cancel₀ (X_sub_C_ne_zero x) h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, map_X, map_C, frobenius_def, pow_succ, pow_mul]
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  have h2 := congrArg (fun q => q.coeff n) hfix
  simp only [coeff_map, frobenius_def] at h2
  obtain ⟨m, hm⟩ := (mem_bot_iff_intCast p (Fbar p)).1 ((Subfield.mem_bot_iff_pow_eq_self (Fbar p) p).2 h2)
  exact ⟨(m : ZMod p), by rw [map_intCast, hm]⟩

theorem exists_labels (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (s : SSParam p ℂ r) :
    ∃ (x : Cyc s.1 → Fbar p) (f : (ZMod p)[X]), Labels L s x f := by
  choose x hx using fun c : Cyc s.1 => exists_labelsChar_of_pos L (cycLen_pos s.1 c) (s.2 c)
  have hl : (∏ y : Σ c : Cyc s.1, Fin (cycLen s.1 c), (X - C (rootElt x y))) ∈
      Polynomial.lifts (algebraMap (ZMod p) (Fbar p)) := by
    rw [Fintype.prod_sigma]
    refine Subsemiring.prod_mem _ fun c _ => ?_
    simp only [rootElt]
    exact prod_frobenius_orbit_mem_lifts (d := cycLen s.1 c) (x := x c) (hx c).1
  obtain ⟨f, hf, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl
    (monic_prod_of_monic _ _ fun y _ => monic_X_sub_C _)
  refine ⟨x, f, hx, fun c => (hx c).1, hm, ?_⟩
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [hf, ← Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map (rootElt x)), Multiset.map_map]
  rfl

end GlobalTheory.ParamLabel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAdaptedBasisQuasiLogarithmsFrameStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_adapted_basis_quasi_logarithms_frame : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∀ (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → ∃ e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q, (∀ l, map Θ (e l) = e0 l) ∧ IsBasis μ' e ∧ IsAdapted F.θ μ' e := by
  first | exact @GlobalTheory.QLog.LiftBasis.exists_lift_isAdapted | exact GlobalTheory.QLog.LiftBasis.exists_lift_isAdapted | (intros; apply GlobalTheory.QLog.LiftBasis.exists_lift_isAdapted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfThinBasisCocycleStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_of_thinBasis_cocycle : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsBas V → IsCoc V hV u → ∃ L : LB X, L.IsLB ∧ IsFrame L V hV u := by
  first | exact @GlobalTheory.ThinGlue.exists_lb_frame | exact GlobalTheory.ThinGlue.exists_lb_frame | (intros; apply GlobalTheory.ThinGlue.exists_lb_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearClosedImmersionProjectiveSpaceCodimTStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_closedImmersion_projectiveSpace_codimTwo : ∀ (F : Type) [Field F] (N : ℕ), ∃ ℓ : PSpace F N ⟶ PSpace F (N + 2), IsClosedImmersion ℓ ∧ ℓ ≫ PSpace.str F (N + 2) = PSpace.str F N ∧ ∀ y, 2 ≤ ringKrullDim ((PSpace F (N + 2)).presheaf.stalk (ℓ y)) := by
  first | exact @GlobalTheory.LinearCodimTwo.exists_linear_closedImmersion_two_le_ringKrullDim_stalk | exact GlobalTheory.LinearCodimTwo.exists_linear_closedImmersion_two_le_ringKrullDim_stalk | (intros; apply GlobalTheory.LinearCodimTwo.exists_linear_closedImmersion_two_le_ringKrullDim_stalk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLubinTatePeriodElementStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lubin_tate_period_element : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → ∃ (ω : AK K) (t u : BK K), thetaK K ω = 0 ∧ ω ∉ RingHom.ker (thetaK K) ^ 2 ∧
      t = toB K (ofA K ω) * (1 + toB K (ofA K ω) * u) ∧ ∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t := by
  first | exact @GlobalTheory.LTPeriodShape.main | exact GlobalTheory.LTPeriodShape.main | (intros; apply GlobalTheory.LTPeriodShape.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledLatticeProdDerivWeierstrassPMemStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescaled_lattice_prodDerivWeierstrassP_mem : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∃ (L' : PeriodPair) (t' : ℂ), Datum p F L' t' ∧ (latticeCurve L').j = (latticeCurve L).j ∧ sqProd p L' t' ∈ F := by
  first | exact @GlobalTheory.CMModel.exists_datum_sqProd_mem | exact GlobalTheory.CMModel.exists_datum_sqProd_mem | (intros; apply GlobalTheory.CMModel.exists_datum_sqProd_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryGroupCharacterOfHeckeCharStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryGroup_character_of_heckeChar : ∀ (D : D7) (ε : AE D), (ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧ (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧ ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0) → ∀ (V : HSp D) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∃ c : GA D V →* Circle, Continuous c ∧ (∀ g ∈ GinfC V, c g = 1) ∧ (∀ v η, NonSplitAt D v η → ∀ g, SuppPl η V g → c g = 1) ∧ ∀ e, IsSplitIdem D e → ∀ g x, SuppAt e V g → IsDetAt e V g x → c g = χ x := by
  first | exact @GlobalTheory.SplitDetCharacter.exists_character | exact GlobalTheory.SplitDetCharacter.exists_character | (intros; apply GlobalTheory.SplitDetCharacter.exists_character <;> assumption)
end

