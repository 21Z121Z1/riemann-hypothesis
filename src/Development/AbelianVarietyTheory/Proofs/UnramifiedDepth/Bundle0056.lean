import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0049
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0050
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SplittingIdempotents
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOfGe
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0052
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LatticeInequalityValuationIntegers

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEigenIdem
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem exists_eigen_idem {O OE κ : Type} [CommRing O] [CommRing OE] [Fintype κ] [DecidableEq κ]
    {m : ℕ} (t : Fin m → (OE →+* O)) (ε : Fin m → O ⊗[ℤ] OE) (hε : CompleteOrthogonalIdempotents ε)
    (he : ∀ i a, (1 ⊗ₜ[ℤ] a) * ε i = t i a • ε i) (ρ : OE →+* Matrix κ κ O) :
    ∃ e : Fin m → Matrix κ κ O, (∀ i j, e i * e j = if i = j then e i else 0) ∧ ∑ i, e i = 1 ∧
      ∀ a i, ρ a * e i = t i a • e i := by
  let Ψ : O ⊗[ℤ] OE →ₐ[O] Matrix κ κ O :=
    Algebra.TensorProduct.lift (Algebra.ofId O _) ρ.toIntAlgHom
      (fun x y => (Algebra.commutes x _ : Commute (Algebra.ofId O (Matrix κ κ O) x) (ρ.toIntAlgHom y)))
  refine ⟨fun i => Ψ (ε i), fun i j => ?_, ?_, fun a i => ?_⟩
  · rw [← map_mul]
    split_ifs with h
    · subst h; rw [(hε.idem i).eq]
    · rw [hε.ortho h, map_zero]
  · rw [← map_sum, hε.complete, map_one]
  · have h1 : Ψ (1 ⊗ₜ[ℤ] a) = ρ a := by
      refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
      rw [map_one, _root_.one_mul]
      rfl
    rw [← h1, ← map_mul, he, map_smul]

private theorem eigen_ext {p : ℕ} [Fact p.Prime] {O OE κ : Type} [CommRing O] [Algebra ℤ_[p] O] [CommRing OE]
    [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →+* Matrix κ κ O)
    (hρ : ∀ c : ℤ_[p], ρ (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] O c • (1 : Matrix κ κ O)) (t : OE →+* O)
    (e : Matrix κ κ O) (h : ∀ a, ρ (1 ⊗ₜ[ℤ] a) * e = t a • e) (x : ℤ_[p] ⊗[ℤ] OE) :
    ρ x * e = tauExt t x • e := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, add_mul, add_smul, hx, hy]
  | tmul c a =>
    have h1 : (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = (c ⊗ₜ[ℤ] 1) * (1 ⊗ₜ[ℤ] a) := by simp
    have h2 : tauExt t (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = algebraMap ℤ_[p] O c * t a := by
      simp [tauExt, Algebra.ofId_apply]
    rw [h2, h1, map_mul, _root_.mul_assoc, h, hρ, smul_mul_assoc, _root_.one_mul, smul_smul]

private theorem frob_ext {p : ℕ} [Fact p.Prime] {O OE : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [CommRing OE] (hp : ¬IsUnit (p : O)) (s t : OE →+* O)
    (h : ∀ a, s a - t a ^ p ∈ IsLocalRing.maximalIdeal O) (x : ℤ_[p] ⊗[ℤ] OE) :
    tauExt s x - tauExt t x ^ p ∈ IsLocalRing.maximalIdeal O := by
  have hp0 : (p : IsLocalRing.ResidueField O) = 0 := by
    have : IsLocalRing.residue O (p : O) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hp
    simpa using this
  haveI : CharP (IsLocalRing.ResidueField O) p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hp0
  have key : ∀ y z : O, y - z ^ p ∈ IsLocalRing.maximalIdeal O ↔
      IsLocalRing.residue O y = frobenius _ p (IsLocalRing.residue O z) := by
    intro y z
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, sub_eq_zero, frobenius_def]
  rw [key]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c a =>
    have h2 : ∀ u : OE →+* O, tauExt u (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = algebraMap ℤ_[p] O c * u a := by
      intro u
      simp [tauExt, Algebra.ofId_apply]
    have h3 := PadicInt.sub_zmodRepr_mem c
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h3
    obtain ⟨d, hd⟩ := h3
    have h4 : IsLocalRing.residue O (algebraMap ℤ_[p] O c) = (c.zmodRepr : IsLocalRing.ResidueField O) := by
      have : c = d * p + c.zmodRepr := by rw [hd]; ring
      conv_lhs => rw [this]
      simp [hp0]
    rw [h2, h2, map_mul, map_mul, map_mul, (key _ _).1 (h a), h4, map_natCast]

private theorem exists_eigB {O OE : Type} [CommRing O] [IsLocalRing O] [CommRing OE] {g m : ℕ}
    (t : Fin m → (OE →+* O)) (hd : ∀ i j, i ≠ j → ∃ a, IsUnit (t i a - t j a))
    (ρ : OE → Matrix (Fin g) (Fin g) O) (e : Fin m → Matrix (Fin g) (Fin g) O)
    (h1 : ∀ i j, e i * e j = if i = j then e i else 0) (h2 : ∑ i, e i = 1)
    (h3 : ∀ a i, ρ a * e i = t i a • e i) (i : Fin m) :
    ∃ (n : ℕ) (W : Fin n → Fin g → O), EigB ρ (t i) W ∧
      Nonempty (LinearMap.range (Matrix.mulVecLin (e i)) ≃ₗ[O] (Fin n → O)) := by
  set N := LinearMap.range (Matrix.mulVecLin (e i)) with hN
  have hid : ∀ w ∈ N, e i *ᵥ w = w := by
    rintro _ ⟨u, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, if_pos rfl]
  haveI : Module.Projective O N :=
    Module.Projective.of_split N.subtype (Matrix.mulVecLin (e i)).rangeRestrict
      (by ext1 w; exact Subtype.ext (hid w w.2))
  haveI : Module.Free O N := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis O N
  have hcomm : ∀ a j, e j * ρ a = t j a • e j := by
    intro a j
    calc e j * ρ a = e j * (ρ a * ∑ k, e k) := by rw [h2, _root_.mul_one]
      _ = ∑ k, t k a • (e j * e k) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [h3, mul_smul_comm]
      _ = t j a • e j := by
        rw [Finset.sum_eq_single j]
        · rw [h1, if_pos rfl]
        · intro k _ hk
          rw [h1, if_neg (Ne.symm hk), smul_zero]
        · simp
  refine ⟨_, fun k => (b k : Fin g → O), ⟨fun k a => ?_, fun w hw => ?_⟩, ⟨b.equivFun⟩⟩
  · have := hid _ (b k).2
    calc ρ a *ᵥ (b k : Fin g → O) = ρ a *ᵥ (e i *ᵥ (b k : Fin g → O)) := by rw [this]
      _ = t i a • (b k : Fin g → O) := by rw [Matrix.mulVec_mulVec, h3, Matrix.smul_mulVec, this]
  · have hz : ∀ j, j ≠ i → e j *ᵥ w = 0 := by
      intro j hj
      obtain ⟨a, ha⟩ := hd j i hj
      have h5 : (t j a - t i a) • (e j *ᵥ w) = 0 := by
        rw [sub_smul, ← Matrix.smul_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul, sub_self]
      exact (ha.smul_eq_zero).1 h5
    have hwN : w ∈ N := by
      refine ⟨w, ?_⟩
      rw [Matrix.mulVecLin_apply]
      calc e i *ᵥ w = ∑ j, e j *ᵥ w := by
            rw [Finset.sum_eq_single i (fun j _ hj => hz j hj) (by simp)]
        _ = w := by rw [← Matrix.sum_mulVec, h2, Matrix.one_mulVec]
    refine ⟨b.equivFun ⟨w, hwN⟩, ?_, fun c hc => ?_⟩
    · have := congrArg Subtype.val (b.sum_equivFun ⟨w, hwN⟩)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, AddSubmonoidClass.coe_finsetSum] using this
    · have : b.equivFun.symm c = ⟨w, hwN⟩ := by
        apply Subtype.ext
        rw [Module.Basis.equivFun_symm_apply]
        simpa using hc
      rw [← this, LinearEquiv.apply_symm_apply]

theorem exists_unramData : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) [IsLocalRing O], H.P = 0 → H.PL = 0 → ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) → ∃ (U : UnramData p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp H) (τ : Fin U.m ≃ (OE →+* O)) (ε : Fin U.m → O ⊗[ℤ] OE), (∀ i x, U.sg i x = tauExt (τ i) x) ∧ (∀ i, U.r i = eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp (τ i))) ∧ CompleteOrthogonalIdempotents ε ∧ (∀ i a, (1 ⊗ₜ[ℤ] a) * ε i = τ i a • ε i) ∧ (∀ i, τ (U.cj i) = (τ i).comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) ∧ ∀ i j, (∀ a, τ j a - τ i a ^ p ∈ IsLocalRing.maximalIdeal O) → U.φ i = j := by
  intro p _ C _ _ _ v O _ _ hv hp _ _ OE _ _ _ _ _ _ cp _ g H _ hP hPL hdisc
  obtain ⟨m, t, ε, φ, hε, he, hd, hφ⟩ := GlobalTheory.SplittingIdempotents.exists_splitting_idempotents_frobenius p C v O hv OE hdisc
  let inc : OE →+* ℤ_[p] ⊗[ℤ] OE := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom
  let ρT : (ℤ_[p] ⊗[ℤ] OE) →+* Matrix (Ix g) (Ix g) O := (algebraMap ℤ_[p] O).mapMatrix.comp H.ρ.toRingHom
  obtain ⟨eT, hT1, hT2, hT3⟩ := exists_eigen_idem (fun i => t i) ε hε he (ρT.comp inc)
  obtain ⟨eL, hL1, hL2, hL3⟩ := exists_eigen_idem (fun i => t i) ε hε he (H.ρL.comp inc)
  have hρT : ∀ c : ℤ_[p], ρT (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] O c • (1 : Matrix (Ix g) (Ix g) O) := by
    intro c
    have : H.ρ (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] _ c := H.ρ.commutes c
    change (H.ρ (c ⊗ₜ[ℤ] 1)).map (algebraMap ℤ_[p] O) = _
    rw [this]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
  have hρL : ∀ c : ℤ_[p], H.ρL (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] O c • (1 : Matrix (Fin g) (Fin g) O) :=
    fun c => (padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).2 g
      (H.ρL.comp (algebraMap ℤ_[p] (ℤ_[p] ⊗[ℤ] OE))) c
  let st : OE →+* OE := ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom
  let cj : Fin m → Fin m := fun i => t.symm ((t i).comp st)
  have hcj : Function.Involutive cj := by
    intro i
    apply t.injective
    ext a
    simp [cj, st]
  have hlt : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O → v (algebraMap O C x) < 1 := by
    intro x hx
    refine lt_of_le_of_ne (hv.map_le_one x) fun h => hx ?_
    exact hv.isUnit_of_one' h
  have hone : ∀ (s : OE →+* O) (a : OE), tauExt (p := p) s (1 ⊗ₜ[ℤ] a) = s a := by
    intro s a
    simp [tauExt]
  refine ⟨{ m := m
            sg := fun i => (tauExt (t i)).toRingHom
            εT := eT
            εL := eL
            cj := hcj.toPerm
            φ := φ
            r := fun i => eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp (t i))
            noPad := ⟨hP, hPL⟩
            εT_orth := hT1
            εT_sum := hT2
            εL_orth := hL1
            εL_sum := hL2
            εT_eig := fun a i => eigen_ext ρT hρT (t i) (eT i) (fun b => hT3 b i) a
            εL_eig := fun a i => eigen_ext H.ρL hρL (t i) (eL i) (fun b => hL3 b i) a
            conj := fun i a => ?_
            frob := fun i a => hlt _ (frob_ext hp.out _ _ (hφ i) a)
            distinct := fun i j hij => ?_
            rank := fun i => ?_ }, t, ε, fun _ _ => rfl, fun _ => rfl, hε, he, fun i => ?_, fun i j h => ?_⟩
  · have h1 : t (hcj.toPerm cj i) = (t i).comp st := t.apply_symm_apply _
    change tauExt (t (hcj.toPerm cj i)) a = tauExt (t i) (sigE p OE a)
    rw [h1]
    exact ((embeddings_idempotents_conjugation p C v O hv OE).2.2 (t i) a).1
  · obtain ⟨a, ha⟩ := hd i j hij
    refine ⟨1 ⊗ₜ[ℤ] a, ?_⟩
    change v (algebraMap O C (tauExt (t i) (1 ⊗ₜ[ℤ] a) - tauExt (t j) (1 ⊗ₜ[ℤ] a))) = 1
    rw [hone, hone]
    exact hv.one_of_isUnit ha
  · obtain ⟨n, W, hW, hn⟩ := exists_eigB (fun i => t i) hd (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) eL hL1 hL2 hL3 i
    have := (eigB_res_surjective C v O hv OE g n _ (t i) W hW).2.2
    rw [← this] at hn
    exact hn
  · exact t.apply_symm_apply _
  · by_contra hne
    obtain ⟨a, ha⟩ := hd (φ i) j hne
    have := Ideal.sub_mem _ (hφ i a) (h a)
    rw [sub_sub_sub_cancel_right] at this
    exact this ha

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfLadicActionLimitStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralEnd_of_ladic_action_limit : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) (I : Fin 2 → Type) (X : RawChart C d I (Fin dd)), (X.lg = fun i => un1 (Y.lg i)) → (X.ex = fun i => un1 (Y.ex i)) → X.h = Y.h → ∀ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd X V M M' ∧ IsEnd X V M' M ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - linAct (Y.B.A.act (a n)) v i)) ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M'.mulVec v i - linAct (Y.B.A.act (star (a n))) v i)) := by
  first | exact @GlobalTheory.ActionLimit.exists_isEnd_of_limit_raw | exact GlobalTheory.ActionLimit.exists_isEnd_of_limit_raw | (intros; apply GlobalTheory.ActionLimit.exists_isEnd_of_limit_raw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralSeriesFrameEqProdRowsStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralSeries_frame_eq_prod_rows : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (Orb : Type) [Fintype Orb] (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] (κ : Type) [Fintype κ] [DecidableEq κ] (X : ∀ o, RawChart C d (I o) κ) (d₀ : ℕ) (I₀ : Fin 2 → Type) [∀ g, Fintype (I₀ g)] (X₀ : RawChart C d₀ I₀ κ), RLaw X₀ V → (∀ o, (X o).ex = X₀.ex ∧ (X o).h = X₀.h ∧ (X o).k = X₀.k) → ∀ (π : Orb → Fin 2 → Matrix κ κ C) (W : Matrix κ κ C), (∀ o g, IntEnd X₀ V (π o g)) → (∀ o g c, (π o g).mulVec ((X o).u g c) = (X o).u g c) → (∀ o g o' g' c, (o, g) ≠ (o', g') → (π o g).mulVec ((X o').u g' c) = 0) → (∑ o, hEnd X₀ (π o 0) (π o 1)) - hEnd X₀ (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) ∈ logInt V κ → ∀ gr : ∀ o, MvPowerSeries (WV (I o)) C, (∀ o, gr o ∈ ExpInt (X o) V) → ∃ F : MvPowerSeries κ C, IntS V F ∧ MvPowerSeries.subst (fun x : κ => MvPowerSeries.subst (fun i : κ => ∑ w : WVO I, (X w.1).u w.2.1 w.2.2 i • (MvPowerSeries.X w : MvPowerSeries (WVO I) C)) (X₀.ex x)) (F * mvExp ((X₀.k : C) • hEnd X₀ 1 W)) = ∏ o, MvPowerSeries.subst (fun w : WV (I o) => (MvPowerSeries.X (⟨o, w⟩ : WVO I) : MvPowerSeries (WVO I) C)) (gr o * mvExp (X o).hRow) := by
  first | exact @GlobalTheory.RowVal.exists_intS_frame_eq_prod | exact GlobalTheory.RowVal.exists_intS_frame_eq_prod | (intros; apply GlobalTheory.RowVal.exists_intS_frame_eq_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTangentChartMatrixOfBasisStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangentChartMatrix_of_basis : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ gb : Module.Basis (Fin g) R₀ B.gg, ∃ S : Matrix (Fin g) (Fin g) (O : Type), IsUnit S ∧ TanMat B O Y gb S := by
  first | exact @GlobalTheory.ChF.exists_tanMat | exact GlobalTheory.ChF.exists_tanMat | (intros; apply GlobalTheory.ChF.exists_tanMat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusMemTypicalCurveSet
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.FrobCurve

variable {C : Type} [Field C]

theorem sum_rescale_tyS {l : ℕ} (hl : l.Prime) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (tyS l fun s => (l : C) * a (s + 1)) =
      ∑ j ∈ Finset.range l, PowerSeries.rescale (ζ ^ j) (tyS l a) := by
  ext n
  simp only [map_sum, PowerSeries.coeff_rescale, ← Finset.sum_mul]
  by_cases hn : l ∣ n
  · obtain ⟨q, rfl⟩ := hn
    have h1 : ∑ j ∈ Finset.range l, (ζ ^ j) ^ (l * q) = (l : C) := by
      have : ∀ j, (ζ ^ j) ^ (l * q) = 1 := fun j => by
        rw [← pow_mul, mul_left_comm, pow_mul, hζ.pow_eq_one, one_pow]
      simp [this]
    rw [h1, Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow hl.pos]
    by_cases hq : ∃ s, l ^ s = q
    · obtain ⟨s, rfl⟩ := hq
      rw [coeff_tyS_pow hl.two_le, ← pow_succ', coeff_tyS_pow hl.two_le]
    · push Not at hq
      rw [coeff_tyS_of_ne _ _ hq, coeff_tyS_of_ne, mul_zero]
      intro s hs
      cases s with
      | zero =>
        rw [pow_zero] at hs
        exact hl.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hs.symm)
      | succ s =>
        rw [pow_succ'] at hs
        exact hq s (Nat.eq_of_mul_eq_mul_left hl.pos hs)
  · have hc : n.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hn).symm
    have h0 : ∑ j ∈ Finset.range l, (ζ ^ j) ^ n = 0 := by
      rw [← (hζ.pow_of_coprime n hc).geom_sum_eq_zero hl.one_lt]
      exact Finset.sum_congr rfl fun j _ => by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [h0, zero_mul, Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow_of_not_dvd hl.pos _ _ hn]

theorem ge_zero_of_pow_eq_one (V : VF C) {ζ : C} {n : ℕ} (hn : 0 < n) (h : ζ ^ n = 1) : V.Ge 0 ζ := by
  have h1 : n • V.v ζ = 0 := by rw [← V.v.map_pow, h, V.v.map_one]
  unfold VF.Ge
  induction hv : V.v ζ using WithTop.recTopCoe with
  | top => exact le_top
  | coe r =>
    rw [hv, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, nsmul_eq_mul] at h1
    have : r = 0 := (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hn.ne')
    rw [this]

theorem rescale_smul' (s c : C) (f : PowerSeries C) :
    PowerSeries.rescale s (c • f) = c • PowerSeries.rescale s f := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

theorem frob_mem_tySet : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, ∀ x ∈ X.TySet V g, Fs V.l x ∈ X.TySet V g := by
  classical
  intro C _ V d _ I _ κ _ X hX g x hx
  haveI := hX.charZero
  haveI := hX.closed
  have hl := V.l_prime
  haveI : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  haveI : NeZero V.l := ⟨hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  obtain ⟨h0, hadd, -, hres⟩ := GlobalTheory.T.gaugedFormalGroupCurveLogarithms_addSubgroup_rescale C V d I κ X hX g
  let lo : (I g ⊕ JJ I g → PowerSeries C) → (κ → PowerSeries C) × (JJ I g → PowerSeries C) := fun A =>
    (fun i => ∑ c : I g, X.u g c i • A (Sum.inl c),
     fun q => A (Sum.inr q) - ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • A (Sum.inl c) else 0)
  have hiff : ∀ y : ℕ → I g ⊕ JJ I g → C,
      y ∈ X.TySet V g ↔ lo (fun n => tyS V.l fun s => y s n) ∈ Cv X V g := fun y => by
    constructor
    · rintro ⟨γ, lam, hγ, hlam, h1, h2⟩
      exact ⟨γ, lam, hγ, hlam, h1, fun q => sub_eq_iff_eq_add.2 (h2 q)⟩
    · rintro ⟨γ, lam, hγ, hlam, h1, h2⟩
      exact ⟨γ, lam, hγ, hlam, h1, fun q => sub_eq_iff_eq_add.1 (h2 q)⟩
  have hsum : ∀ (M : ℕ) (f : ℕ → (κ → PowerSeries C) × (JJ I g → PowerSeries C)),
      (∀ j, f j ∈ Cv X V g) → ∑ j ∈ Finset.range M, f j ∈ Cv X V g := fun M f hf =>
    Finset.sum_induction f (· ∈ Cv X V g) (fun a b ha hb => hadd a ha b hb) h0 fun j _ => hf j
  have hint : ∀ j, V.Ge 0 (ζ ^ j) := fun j => (ge_zero_of_pow_eq_one V hl.pos hζ.pow_eq_one).pow j
  have hS := hsum V.l _ fun j => hres (ζ ^ j) (hint j) _ ((hiff x).1 hx)
  rw [hiff]
  refine GlobalTheory.RowLaw.mem_Cv_of_subst_X_pow C V d I κ X hX g V.l hl.pos _ ?_
  have hsub : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ V.l) :=
    PowerSeries.HasSubst.X_pow hl.ne_zero
  have key : ∀ n, PowerSeries.substAlgHom (R := C) hsub (tyS V.l fun s => Fs V.l x s n) =
      ∑ j ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ j) (tyS V.l fun s => x s n) := fun n => by
    rw [PowerSeries.coe_substAlgHom]
    exact sum_rescale_tyS hl hζ fun s => x s n
  convert hS using 1
  refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
  · simp only [lo, Prod.fst_sum, Finset.sum_apply, ← PowerSeries.coe_substAlgHom hsub, map_sum, map_smul, key,
      rescale_smul', Finset.smul_sum]
    exact Finset.sum_comm
  · simp only [lo, Prod.snd_sum, Finset.sum_apply, ← PowerSeries.coe_substAlgHom hsub, map_sum, map_sub, key,
      Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · simp only [map_smul, key, rescale_smul', Finset.smul_sum]
    · simp

end GlobalTheory.RowLaw.FrobCurve
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndPairPlaces
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.TeichPair

theorem hasTeich : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ g, HasTeich (Y.raw p) V g := by
  intro C _ _ V O _ _ dd Y d _ I _ p g
  obtain ⟨s, N, ζ, hs, hN, h1, h2, h3, hζ⟩ := exists_seq V Y.cpl (p.em g) (p.em_int g) (p.em_frob g)
    (fun a a' h => p.em_sep (g, a) (g, a') fun h' => h (congrArg Prod.snd h')) (p.em_unr g)
  obtain ⟨M, M', hM, -, hl, hl'⟩ := GlobalTheory.T.exists_adjointIntegralEnd_of_ladicLimit C V O dd Y d I p s hs
  have key : ∀ (a : ZMod d) (z w : C), V.Ge 0 w →
      (∀ N : ℕ, ∃ n0, ∀ n ≥ n0, V.Ge N (z - p.em g a (s n) * w)) → z = ζ a * w := fun a z w hw h => by
    rw [← sub_eq_zero]
    refine eq_zero_of_ge (V := V) fun n => ?_
    obtain ⟨n0, hn⟩ := h n
    have e1 := hn (max n0 n) (le_max_left _ _)
    have e2 := (hw.mul_int (hζ a (max n0 n))).mono (w' := n) (by exact_mod_cast le_max_right _ _)
    have := e1.sub e2
    convert this using 1
    ring
  have hconj : ∀ a x, p.em (1 - g) a (star x) = p.em g a x := fun a x => by
    fin_cases g
    · show p.em 1 a (star x) = p.em 0 a x
      rw [p.em_conj, star_star]
    · show p.em 0 a (star x) = p.em 1 a x
      rw [p.em_conj]
  refine ⟨N, ζ, M, M', hN, h1, h2, h3, hM, fun c => funext fun i => ?_, fun q => funext fun i => ?_⟩
  · refine key _ _ _ (p.u_int g c i) fun n => ?_
    have := hl n (p.u g c) i
    simp only [p.u_eig] at this
    exact this
  · refine key _ _ _ (p.u_int (1 - g) q i) fun n => ?_
    have := hl' n (p.u (1 - g) q) i
    simp only [p.u_eig, hconj] at this
    exact this

end GlobalTheory.TeichPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateDatumHypothesesPeriodTowerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTate_datum_hypotheses_period_tower : ∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE], HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) (show O from (Ainf.ainfTowerL p O hv ε hε).c) := by
  first | exact @GlobalTheory.ChF.hodgeTateSetting_ainfTower_of_isPrimitiveRoot | exact GlobalTheory.ChF.hodgeTateSetting_ainfTower_of_isPrimitiveRoot | (intros; apply GlobalTheory.ChF.hodgeTateSetting_ainfTower_of_isPrimitiveRoot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JacobianMulTangentChartMatrixIntertwinesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobian_mul_tangentChartMatrix_intertwines : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (O : Type)), TanMat B O Y gb S → ∀ (A : OEnd B O) (α : Fin g → PS (O : Type) 1 g) (ρ : Matrix (Fin g) (Fin g) (O : Type)), (∀ j, MvPowerSeries.constantCoeff (α j) = 0) → (∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a])) → (∀ {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (ρ k l) * i) → A.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)) → lin α * S = S * ρ := by
  first | exact @GlobalTheory.ChF.lin_mul_tanMat | exact GlobalTheory.ChF.lin_mul_tanMat | (intros; apply GlobalTheory.ChF.lin_mul_tanMat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LatticeInequalityValuationIntegersStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_inequality_valuation_integers : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → (∃ c : C, 0 < v c ∧ v c < 1) → ∀ (n s h : ℕ) (a : Fin n → O), Function.Injective a → ∀ (M : Submodule O (Fin n × Fin s → O)), M.FG → (∀ f ∈ M, (fun y : Fin n × Fin s => a y.1 * f y) ∈ M) → (∀ (τ : Fin n) (z : Fin s → O), ∃ f ∈ M, ∀ i, f (τ, i) = z i) → ∀ (φ : Fin h → Fin n × Fin s → O), (∀ l, φ l ∈ M) → ∀ c : NNReal, c ≠ 0 → HasLen v O (M ⧸ (Submodule.span O (Set.range fun q : Fin n × Fin h => fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y)).comap M.subtype) c → ∃ x : Fin n → NNReal, (∀ τ, HasLen v O ((Fin s → O) ⧸ Submodule.span O (Set.range fun l => fun i => φ l (τ, i))) (x τ)) ∧ c ^ 2 * v (discr fun τ => algebraMap O C (a τ)) ^ h ≤ (∏ τ, x τ) ^ 2 * v (discr fun τ => algebraMap O C (a τ)) ^ s := by
  first | exact @GlobalTheory.ChF.lattice_ineq_integers | exact GlobalTheory.ChF.lattice_ineq_integers | (intros; apply GlobalTheory.ChF.lattice_ineq_integers <;> assumption)
end

