import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantFrameCommutesCartan
section
noncomputable section

namespace GlobalTheory.MajFrameCartan

open scoped TensorProduct Matrix ComplexOrder
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

theorem isCartanInv_transpose {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (h : IsCartan M θ) :
    Formalism.IndefR.Datum.IsCartanInv Mᵀ θ := by
  obtain ⟨h1, h2, h3⟩ := h
  have h2' : θᴴ * Mᵀ * θ = Mᵀ := by
    have := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.transpose_map] at this
    show θᵀ.map star * Mᵀ * θ = Mᵀ
    rw [Matrix.mul_assoc]
    exact this
  have hMt : (Mᵀ)ᴴ = Mᵀ := by
    ext i j
    have := congrFun (congrFun hM j) i
    simpa [Matrix.conjTranspose_apply] using this
  have hH : (Mᵀ * θ)ᴴ = Mᵀ * θ := by
    rw [Matrix.conjTranspose_mul, hMt]
    calc θᴴ * Mᵀ = θᴴ * Mᵀ * (θ * θ) := by rw [h1, Matrix.mul_one]
      _ = (θᴴ * Mᵀ * θ) * θ := by simp only [Matrix.mul_assoc]
      _ = Mᵀ * θ := by rw [h2']
  refine ⟨h1, h2', Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hH, fun x hx => ?_⟩⟩
  have e : star x ⬝ᵥ ((Mᵀ * θ) *ᵥ x) = (θ *ᵥ x) ⬝ᵥ (M *ᵥ star x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  have him := Matrix.IsHermitian.im_star_dotProduct_mulVec_self (A := Mᵀ * θ) hH x
  refine Complex.pos_iff.mpr ⟨?_, ?_⟩
  · rw [e]; exact h3 x hx
  · simpa using him.symm

theorem exists_majorantFrame_commute : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∃ a : GL (Fin n) (AF F ⊗[F] E), IsMajorantFrame σ X.Jᵀ a ∧ ∀ (w : InfinitePlace F) (k : GArch σ X.Jᵀ w),
      k ∈ stabArch σ X.Jᵀ w (bc (compInf F E w) a) →
        Commute ((matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w))) (X.θ w) := by
  intro F E _ _ _ _ _ σ B n X r s hB hX
  have hcm := hB.cm
  have hM : ∀ w : InfinitePlace F, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← hcm.2.2.2 (B.emb w).1, hX.herm]
  have hC : ∀ w : InfinitePlace F, Formalism.IndefR.Datum.IsCartanInv (X.Jᵀ.map (B.emb w).1) (X.θ w) := fun w => by
    rw [Matrix.transpose_map]
    exact isCartanInv_transpose (hM w) (hX.cartan w)
  choose b ε h1 h2 using fun w => GlobalTheory.Doubling.exists_frame_of_isCartanInv (hC w)
  let e := fun w : InfinitePlace F => RingEquiv.ofBijective _ (infEmb_bijective hcm (B.emb w))
  let c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E) := fun w => bc (e w).symm.toRingHom (b w)
  have hc : ∀ w, (c w).1.map (infEmb (B.emb w)) = (b w).1 := fun w =>
    Matrix.ext fun i j => (e w).apply_symm_apply _
  have hc' : ∀ w, ((c w)⁻¹).1.map (infEmb (B.emb w)) = ((b w)⁻¹).1 := fun w => by
    rw [show (c w)⁻¹ = bc (e w).symm.toRingHom (b w)⁻¹ from (map_inv _ _).symm]
    exact Matrix.ext fun i j => (e w).apply_symm_apply _
  obtain ⟨a, -, ha⟩ := GlobalTheory.AdelicU.Frames.exists_GL_of_components (F := F) (E := E) (n := n) ∅ (fun _ => 1)
    (fun _ _ => rfl) c
  refine ⟨a, fun w => ⟨ε w, ?_⟩, fun w k hk => ?_⟩
  · rw [ha w, GlobalTheory.Doubling.frame_local_iff hcm (B.emb w) X.Jᵀ (c w).1 (ε w), hc]
    exact h1 w
  · have hK : ((matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w)))ᴴ * X.Jᵀ.map (B.emb w).1 *
        (matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w)) = X.Jᵀ.map (B.emb w).1 :=
      (archEquiv X.Jᵀ hcm (B.emb w) k).2
    have hbc : (b w).1 * ((b w)⁻¹).1 = 1 := Units.mul_inv _
    have key : ∀ x : GL (Fin n) (w.Completion ⊗[F] E), x ∈ UJ (sigR w.Completion σ) 1 →
        (x.1.map (infEmb (B.emb w)))ᴴ * x.1.map (infEmb (B.emb w)) = 1 := fun x hx => by
      have hx' : cT (sigR w.Completion σ) x.1 * 1 * x.1 = 1 := hx
      have := congrArg (fun y => y.map (infEmb (B.emb w))) hx'
      simpa only [mul_one, Matrix.map_mul, Frames.map_cT_sigR hcm, Matrix.map_one _ (map_zero _) (map_one _)]
        using this
    rw [mem_stabArch, ha w] at hk
    have hu := key _ hk
    rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hc, hc'] at hu
    have := (GlobalTheory.Doubling.unitary_iff_commute hbc (h1 w) (GlobalTheory.Doubling.diagonal_sign_mul_self (ε w)) hK).1 hu
    rwa [h2 w] at this

end GlobalTheory.MajFrameCartan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLine
section
noncomputable section

namespace GlobalTheory.KBridge

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def infT : AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)

variable (F E) in

def finT : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)

variable (F E) in

def ofInfT : Ainf F ⊗[F] E →ₗ[F] AF F ⊗[F] E := (LinearMap.inl F (Ainf F) (Af F)).rTensor E

variable (F E) in

def ofFinT : Af F ⊗[F] E →ₗ[F] AF F ⊗[F] E := (LinearMap.inr F (Ainf F) (Af F)).rTensor E

theorem decomp (z : AF F ⊗[F] E) : z = ofInfT F E (infT F E z) + ofFinT F E (finT F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add]
    conv_lhs => rw [hx, hy]
    abel
  | tmul a e =>
    change a ⊗ₜ[F] e = ((a.1, 0) : AF F) ⊗ₜ[F] e + ((0, a.2) : AF F) ⊗ₜ[F] e
    rw [← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext (add_zero _).symm (zero_add _).symm

theorem tmul_eq_smul_incV {n : ℕ} (a : AF F) (x : Fin n → E) : (fun i => a ⊗ₜ[F] x i) = a • incV F x := by
  funext i
  change a ⊗ₜ[F] x i = a • ((1 : AF F) ⊗ₜ[F] x i)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem infT_tmul (a : AF F) (e : E) : infT F E (a ⊗ₜ[F] e) = a.1 ⊗ₜ[F] e := rfl

theorem mem_latHat_iff {n : ℕ} (X : Spc F E n) (z : Fin n → AE F E) :
    z ∈ latHat X ↔ (∀ i, infT F E (z i) = 0) ∧
      (fun i => finT F E (z i)) ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)) := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hv, x, hx, rfl⟩ := hz
      have h0 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 ha
      rw [← tmul_eq_smul_incV]
      refine ⟨fun i => ?_, ?_⟩
      · rw [infT_tmul, h0, TensorProduct.zero_tmul]
      · exact AddSubgroup.subset_closure ⟨a.2, fun v => hv v, x, hx, rfl⟩
    | zero =>
      refine ⟨fun i => map_zero _, ?_⟩
      have e : (fun i => finT F E ((0 : Fin n → AE F E) i)) = 0 := funext fun i => map_zero _
      rw [e]; exact zero_mem _
    | add y z _ _ hy hz =>
      refine ⟨fun i => ?_, ?_⟩
      · rw [Pi.add_apply, map_add, hy.1 i, hz.1 i, add_zero]
      · have e : (fun i => finT F E ((y + z) i)) = (fun i => finT F E (y i)) + fun i => finT F E (z i) :=
          funext fun i => map_add _ _ _
        rw [e]; exact add_mem hy.2 hz.2
    | neg y _ hy =>
      refine ⟨fun i => ?_, ?_⟩
      · rw [Pi.neg_apply, map_neg, hy.1 i, neg_zero]
      · have e : (fun i => finT F E ((-y) i)) = -fun i => finT F E (y i) := funext fun i => map_neg _ _
        rw [e]; exact neg_mem hy.2
  · rintro ⟨hi, hf⟩
    have e : z = fun i => ofFinT F E (finT F E (z i)) := funext fun i => by
      conv_lhs => rw [decomp (z i)]
      rw [hi i, map_zero, zero_add]
    rw [e]
    suffices H : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)), (fun i => ofFinT F E (y i)) ∈ latHat X from H _ hf
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨show AF F from (0, a), map_zero _, fun v => ha v, x, hx, tmul_eq_smul_incV (show AF F from (0, a)) x⟩
    | zero =>
      have e : (fun i => ofFinT F E ((0 : Fin n → Af F ⊗[F] E) i)) = 0 := funext fun i => map_zero _
      rw [e]; exact zero_mem _
    | add y y' _ _ hy hy' =>
      have e : (fun i => ofFinT F E ((y + y') i)) = (fun i => ofFinT F E (y i)) + fun i => ofFinT F E (y' i) :=
        funext fun i => map_add _ _ _
      rw [e]; exact add_mem hy hy'
    | neg y _ hy =>
      have e : (fun i => ofFinT F E ((-y) i)) = -fun i => ofFinT F E (y i) := funext fun i => map_neg _ _
      rw [e]; exact neg_mem hy

theorem mulVec_mem_latHat {n : ℕ} (σ : E →ₐ[F] E) (X : Spc F E n) (hfg : X.L.FG) {k : GAd σ X.Jᵀ}
    (hk : k ∈ levelOpen σ X.Jᵀ X.L) {z : Fin n → AE F E} (hz : z ∈ latHat X) :
    (matHom (AF F) σ X.Jᵀ k).1 *ᵥ z ∈ latHat X := by
  rw [mem_latHat_iff] at hz ⊢
  obtain ⟨hi, hf⟩ := hz
  refine ⟨fun i => ?_, ?_⟩
  · have e : ((infT F E).toRingHom ∘ z) = 0 := funext fun j => hi j
    refine (RingHom.map_mulVec (infT F E).toRingHom (matHom (AF F) σ X.Jᵀ k).1 z i).trans ?_
    rw [e, Matrix.mulVec_zero]
    rfl
  · have e : (fun i => finT F E (((matHom (AF F) σ X.Jᵀ k).1 *ᵥ z) i)) =
        Formalism.MainNotions.StandardLattice.finMat σ X.Jᵀ k *ᵥ fun i => finT F E (z i) :=
      funext fun i => RingHom.map_mulVec (finT F E).toRingHom _ _ i
    rw [e]
    exact ((mem_levelOpen_iff_latHat σ X.Jᵀ hfg k).1 hk _).1 hf

theorem ofGAd_mem_stabK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), X.L.IsLattice E → ∀ g : GAd σ X.Jᵀ,
    (∀ w, Commute ((matHom w.Completion σ X.Jᵀ (projArch σ X.Jᵀ w g)).1.map (infEmb (B.emb w))) (X.θ w)) →
    (∀ v, proj σ X.Jᵀ v g ∈ stabLoc σ X.Jᵀ X.L v) → GlobalTheory.IwLine.ofGAd σ X.J g ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X := by
  intro F E _ _ _ _ _ σ B n X hL g h1 h2
  have hfg : X.L.FG := hL.fg
  have hg : g ∈ levelOpen σ X.Jᵀ X.L := mem_levelOpen.2 h2
  refine ⟨fun w => h1 w, fun z hz => ⟨?_, ?_⟩⟩
  · rw [GlobalTheory.IwLine.mat_ofGAd]
    exact mulVec_mem_latHat σ X hfg hg hz
  · rw [← map_inv, GlobalTheory.IwLine.mat_ofGAd]
    exact mulVec_mem_latHat σ X hfg (inv_mem hg) hz

end GlobalTheory.KBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsEquivDefiniteFieldPairsOdd
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.Move

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem aeval_conj (y : G.Cˣ) (x : G.C) (A : Polynomial G.F) :
    Polynomial.aeval ((y : G.C) * x * ((y⁻¹ : G.Cˣ) : G.C)) A =
      (y : G.C) * Polynomial.aeval x A * ((y⁻¹ : G.Cˣ) : G.C) := by
  have hp : ∀ k : ℕ, ((y : G.C) * x * ((y⁻¹ : G.Cˣ) : G.C)) ^ k =
      (y : G.C) * x ^ k * ((y⁻¹ : G.Cˣ) : G.C) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [mul_assoc, Units.inv_mul_cancel_left]
  induction A using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, map_add, hf, hg, mul_add, add_mul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, hp n, ← mul_assoc, ← mul_assoc,
      Algebra.commutes a (y : G.C)]
    simp only [mul_assoc]

theorem move (y : G.Cˣ) (s : ℚ) (g b b' : G.C) (A : Polynomial G.F)
    (hb : b' = algebraMap ℚ G.C s * (y * b * sh G y)) :
    Polynomial.aeval ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)) A * b' =
      algebraMap ℚ G.C s * (y * (Polynomial.aeval g A * b) * sh G y) := by
  rw [aeval_conj, hb, ← mul_assoc, ← Algebra.commutes s]
  simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem cancel {R : Type*} [Ring R] (X w : R) (b u : Rˣ) (hu : X * b = u) (h : X * b = X * w) :
    (b : R) = w := by
  have hX : X = (u : R) * ((b⁻¹ : Rˣ) : R) := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  have hl : (b : R) * ((u⁻¹ : Rˣ) : R) * X = 1 := by
    rw [hX, mul_assoc, ← mul_assoc ((u⁻¹ : Rˣ) : R), Units.inv_mul, one_mul, Units.mul_inv]
  calc (b : R) = ((b : R) * ((u⁻¹ : Rˣ) : R) * X) * b := by rw [hl, one_mul]
    _ = ((b : R) * ((u⁻¹ : Rˣ) : R) * X) * w := by rw [mul_assoc _ X, h, ← mul_assoc]
    _ = w := by rw [hl, one_mul]

private theorem minpoly_monic_of_irreducible (x : G.C)
    (hi : Irreducible (minpoly G.F x)) : (minpoly G.F x).Monic := by
  have hint : IsIntegral G.F x := by
    by_contra h
    exact hi.ne_zero (minpoly.eq_zero h)
  exact minpoly.monic hint

private theorem aeval_eq_zero_of_aeval_conj_eq_zero (y : G.Cˣ) (g : G.C)
    (q : Polynomial G.F) (h : Polynomial.aeval ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)) q = 0) :
    Polynomial.aeval g q = 0 := by
  rw [aeval_conj] at h
  calc Polynomial.aeval g q
      = ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * Polynomial.aeval g q * ((y⁻¹ : G.Cˣ) : G.C)) * (y : G.C) := by
        simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
    _ = 0 := by rw [h, mul_zero, zero_mul]

private theorem minpoly_conj_eq_of_irreducible (y : G.Cˣ) (g : G.C)
    (hi : Irreducible (minpoly G.F ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)))) :
    minpoly G.F ((y : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C)) = minpoly G.F g :=
  minpoly.eq_of_irreducible_of_monic hi (aeval_eq_zero_of_aeval_conj_eq_zero y g _ (minpoly.aeval _ _))
    (minpoly_monic_of_irreducible _ hi)

end GlobalTheory.LKDef.Move

namespace GlobalTheory.LKDef

open GlobalTheory.LKDef.Move

theorem cls_equiv_dcls_irr : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (sel : Polynomial G.F → ℂ), IsSel G sel → ∃ e : {q : Cls G // Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol)} ≃ {q : DCls G // Irreducible (Quot.out q).pol}, ∀ q, (Quot.out (e q).1).pol = (Quot.out q.1).pol ∧ ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → (Quot.out (e q).1).term Kf f r K φ = (Quot.out q.1).term Kf f r K φ := by
  intro p hp G ha hn sel hsel
  obtain ⟨v0, hv0⟩ : ∃ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 := by
    have h1 : 0 < G.a := by rw [ha]; exact Nat.one_pos
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp h1
    exact ⟨x.1, x.2⟩
  have key := fun (P0 : Polynomial G.F) (hi : Irreducible P0) (hm : P0.Monic)
      (hd : P0.natDegree = G.n) =>
    GlobalTheory.T.exists_polynomial_move_definiteSimilitudePair_marked p G ha hn P0 (sel P0) v0 hv0 hi (hsel v0 hv0 P0 hm hd)
  choose! A hA1 hA2 using key
  have hF := fun (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)) =>
    hA2 P.pol hi (minpoly_monic_of_irreducible (P.γ : G.C) hi) P.reg.1 P rfl hm
  choose FQ hFγ hFc hFβ hFu using hF
  have hB := fun (Q : DPair G) (hi : Irreducible Q.pol) =>
    hA1 Q.pol hi (minpoly_monic_of_irreducible (Q.γ : G.C) hi) Q.reg.1 Q rfl
  choose BP hBγ hBc hBβ hBm hBu using hB

  have hpolP : ∀ P P' : Pair G, P'.Rel P → Irreducible P.pol → P'.pol = P.pol := by
    intro P P' hr hi
    obtain ⟨y, s, -, -, hγ⟩ := hr
    have e : (P.γ : G.C) = (y : G.C) * P'.γ * ((y⁻¹ : G.Cˣ) : G.C) := by
      rw [hγ, Units.val_mul, Units.val_mul]
    have hi' : Irreducible (minpoly G.F ((y : G.C) * P'.γ * ((y⁻¹ : G.Cˣ) : G.C))) := by
      rw [← e]; exact hi
    show minpoly G.F (P'.γ : G.C) = minpoly G.F (P.γ : G.C)
    rw [e]
    exact (minpoly_conj_eq_of_irreducible y _ hi').symm
  have hFirr : ∀ (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)),
      Irreducible (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).pol := by
    intro P hi hm
    rw [DPair.pol_eq_of_rel (DPair.rel_out (FQ P hi hm))]
    show Irreducible (minpoly G.F ((FQ P hi hm).γ : G.C))
    rw [hFγ P hi hm]
    exact hi
  have hBok : ∀ (Q : DPair G) (hi : Irreducible Q.pol),
      Irreducible (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol ∧
      (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).Mark
        (sel (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol) := by
    intro Q hi
    have hr := (Pair.mk_eq_iff_rel_and_out_rel p G (BP Q hi) (BP Q hi)).2
    have hPpol : (BP Q hi).pol = Q.pol := by
      show minpoly G.F ((BP Q hi).γ : G.C) = minpoly G.F (Q.γ : G.C)
      rw [hBγ Q hi]
    have hPi : Irreducible (BP Q hi).pol := by rw [hPpol]; exact hi
    rw [hpolP _ _ hr hPi, Pair.mark_iff_of_rel p G _ _ _ hr, hPpol]
    exact ⟨hi, hBm Q hi⟩

  have hleft : ∀ (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)),
      P.Rel (BP _ (hFirr P hi hm)) := by
    intro P hi hm
    obtain ⟨y, s, hs, hβ, hγ⟩ := DPair.rel_out (FQ P hi hm)
    have hpol : (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).pol = P.pol := by
      rw [DPair.pol_eq_of_rel (DPair.rel_out (FQ P hi hm))]
      show minpoly G.F ((FQ P hi hm).γ : G.C) = minpoly G.F (P.γ : G.C)
      rw [hFγ P hi hm]
    refine ⟨y, s, hs, ?_, ?_⟩
    · rw [hBβ _ (hFirr P hi hm), hpol, hγ, Units.val_mul, Units.val_mul,
        GlobalTheory.LKDef.Move.move y s ((FQ P hi hm).γ : G.C) _ _ (A P.pol) hβ, hFγ P hi hm, ← hFβ P hi hm]
    · rw [hBγ _ (hFirr P hi hm), hγ, hFγ P hi hm]

  have hright : ∀ (Q : DPair G) (hi : Irreducible Q.pol),
      (FQ _ (hBok Q hi).1 (hBok Q hi).2).Rel Q := by
    intro Q hi
    have hr := (Pair.mk_eq_iff_rel_and_out_rel p G (BP Q hi) (BP Q hi)).2
    have hPpol : (BP Q hi).pol = Q.pol := by
      show minpoly G.F ((BP Q hi).γ : G.C) = minpoly G.F (Q.γ : G.C)
      rw [hBγ Q hi]
    have hPi : Irreducible (BP Q hi).pol := by rw [hPpol]; exact hi
    have hP'pol : (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol = Q.pol := by
      rw [hpolP _ _ hr hPi, hPpol]
    have hA' : A (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).pol = A Q.pol := by
      rw [hP'pol]
    obtain ⟨y, s, hs, hβ, hγ⟩ := id hr
    have hc : (y : G.C) * (Quot.out (Quot.mk (Pair.Rel (G := G)) (BP Q hi) : Cls G)).γ *
        ((y⁻¹ : G.Cˣ) : G.C) = Q.γ := by
      rw [← hBγ Q hi, hγ, Units.val_mul, Units.val_mul]
    refine ⟨y, s, hs, ?_, ?_⟩
    · refine GlobalTheory.LKDef.Move.cancel (Polynomial.aeval (Q.γ : G.C) (A Q.pol)) _ Q.β (BP Q hi).β
        (hBβ Q hi).symm ?_
      rw [← hBβ Q hi, hβ, hFβ _ (hBok Q hi).1 (hBok Q hi).2,
        ← GlobalTheory.LKDef.Move.move y s _ _ _ _ rfl, hc, hA']
    · rw [hFγ _ (hBok Q hi).1 (hBok Q hi).2, ← hBγ Q hi, hγ]

  have hterm : ∀ (P : Pair G) (hi : Irreducible P.pol) (hm : P.Mark (sel P.pol)),
      (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).pol = P.pol ∧
      ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r →
        (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) →
        (Quot.out (Quot.mk (DPair.Rel (G := G)) (FQ P hi hm) : DCls G)).term Kf f r K φ =
          P.term Kf f r K φ := by
    intro P hi hm
    have h9 := GlobalTheory.T.related_pairs_orbital_term_eq p G (FQ P hi hm) _ (DPair.rel_out (FQ P hi hm))
    refine ⟨?_, fun Kf f r K φ hr hf hφ => ?_⟩
    · rw [← h9.1]
      show minpoly G.F ((FQ P hi hm).γ : G.C) = minpoly G.F (P.γ : G.C)
      rw [hFγ P hi hm]
    · rw [← h9.2.2 Kf f r K φ hr hf hφ]
      exact (GlobalTheory.T.kottwitzTerm_eq_definitePair_of_local_isometry p G P (FQ P hi hm) (hFγ P hi hm).symm (hFc P hi hm).symm (hFu P hi hm)
        Kf f r K φ hr hf hφ).symm
  refine ⟨⟨fun q => ⟨(Quot.mk (DPair.Rel (G := G)) (FQ _ q.2.1 q.2.2) : DCls G), hFirr _ q.2.1 q.2.2⟩,
    fun q => ⟨(Quot.mk (Pair.Rel (G := G)) (BP _ q.2) : Cls G), hBok _ q.2⟩, fun q => ?_, fun q => ?_⟩,
    fun q => hterm _ q.2.1 q.2.2⟩
  · apply Subtype.ext
    exact ((Pair.mk_eq_iff_rel_and_out_rel p G _ _).1.mpr (hleft _ q.2.1 q.2.2)).symm.trans
      (Quot.out_eq q.1)
  · apply Subtype.ext
    exact ((DPair.mk_eq_iff _ _).mpr (hright _ q.2)).trans (Quot.out_eq q.1)
end GlobalTheory.LKDef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

open scoped Pointwise

namespace GlobalTheory.ThKOrthVInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isHermND_smul_of_skew {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hsk : ∀ k l, σ (J l k) = -J k l) (hd : J.det ≠ 0) {c : E} (hc : c ≠ 0) (hcs : σ c = -c) :
    IsHermND σ (c • J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · have h1 : σ (J i j) = -J j i := hsk j i
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hcs, hσ, h1]
    ring
  · have e : (J.map σ).det = (σ : E →+* E) J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e]
    exact mul_ne_zero (pow_ne_zero _ hc) ((map_ne_zero _).2 hd)

theorem measure_fundDom_lt_top_smul (hP : GlobalTheory.Published.SiegelSetUnitary) {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {c : E} (hc : c ≠ 0) (hJ : IsHermND σ (c • J.map σ)) {μ : Measure (UA σ J)}
    [μ.IsHaarMeasure] {D : Set (UA σ J)} (hD : IsFundamentalDomain (ratU σ J) D μ) : μ D < ⊤ := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have heq : UG (cA σ) (incM F J) = HR (AF F) σ (c • J.map σ) := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ hc
  let e : UA σ J ≃* GAd σ (c • J.map σ) := MulEquiv.subgroupCongr heq
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  obtain ⟨S, hSc, hcov, -, hfin, -⟩ := GlobalTheory.SiegelSet.exists_cover hP hcm hJ
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ J) := ⟨by
    have h3 : (fun p : UA σ J × UA σ J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  have hH : (μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e he he'
  have h1 : μ (e ⁻¹' S) < ⊤ := by
    have h2 := hfin _ hH
    rwa [Measure.map_apply he.measurable hSc.measurableSet] at h2
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ J
  haveI : MeasurableMul (UA σ J) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI : MeasurableConstSMul (ratU σ J) (UA σ J) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : UA σ J => γ.1 * x).measurable⟩
  haveI : SMulInvariantMeasure (ratU σ J) (UA σ J) μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩
  have hcov' : D ⊆ ⋃ γ : ratU σ J, γ • (e ⁻¹' S) ∩ D := by
    intro x hx
    obtain ⟨γ, hγ, s, hs, hxs⟩ := hcov (e x)
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
    have hr : e.symm γ ∈ ratU σ J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
    refine Set.mem_iUnion.2 ⟨⟨e.symm γ, hr⟩, Set.mem_smul_set.2 ⟨e.symm s, show e (e.symm s) ∈ S by rw [MulEquiv.apply_symm_apply]; exact hs, ?_⟩, hx⟩
    change e.symm γ * e.symm s = x
    rw [← map_mul, ← hxs, MulEquiv.symm_apply_apply]
  calc μ D ≤ μ (⋃ γ : ratU σ J, γ • (e ⁻¹' S) ∩ D) := measure_mono hcov'
    _ ≤ ∑' γ : ratU σ J, μ (γ • (e ⁻¹' S) ∩ D) := measure_iUnion_le _
    _ = μ (e ⁻¹' S) := (hD.measure_eq_tsum _).symm
    _ < ⊤ := h1

theorem norm_le_qht_of_le_ht {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : UA σ J → ℂ}
    (hgi : ∀ γ ∈ ratU σ J, ∀ x, g (γ * x) = g x) {C : ℝ} {k : ℕ} (hC : ∀ h, ‖g h‖ ≤ C * (ht h : ℝ) ^ k) (h : UA σ J) :
    ‖g h‖ ≤ max C 0 * (qht h : ℝ) ^ k := by
  let M : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have e1 : M * qht h ^ k = ⨅ γ : ratU σ J, M * ht (γ.1 * h) ^ k :=
    Monotone.map_ciInf_of_continuousAt (f := fun x : ℝ≥0 => M * x ^ k)
      ((continuous_const.mul (continuous_pow k)).continuousAt)
      (fun x y hxy => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hxy k) (by positivity))
      (OrderBot.bddBelow _)
  have e2 : ‖g h‖₊ ≤ M * qht h ^ k := by
    rw [e1]
    refine le_ciInf fun γ => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, ← hgi γ.1 γ.2 h]
    refine (hC _).trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have e3 := NNReal.coe_le_coe.2 e2
  push_cast at e3
  exact e3

end GlobalTheory.ThKOrthVInt
end
end

