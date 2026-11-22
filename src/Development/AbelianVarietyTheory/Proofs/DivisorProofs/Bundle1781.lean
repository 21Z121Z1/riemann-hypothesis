import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1743
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1745
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Decomposition
section
open Matrix

namespace GlobalTheory.UnipotentCongruenceInverse

section Ring
variable {R M : Type} [CommRing R] [Ring M] [Algebra R M]

theorem cong_mul {e : R} {x y : M} (hx : (1 - e) • (x - 1) = 0) (hy : (1 - e) • (y - 1) = 0) :
    (1 - e) • (x * y - 1) = 0 := by
  have h1 : x * y - 1 = (x - 1) * y + (y - 1) := by noncomm_ring
  rw [h1, smul_add, ← smul_mul_assoc, hx, zero_mul, zero_add, hy]

theorem cong_inv {e : R} {x y : M} (hx : (1 - e) • (x - 1) = 0) (hxy : y * x = 1) :
    (1 - e) • (y - 1) = 0 := by
  have h1 : y - 1 = -(y * (x - 1)) := by rw [mul_sub, hxy, mul_one]; abel
  rw [h1, smul_neg, ← mul_smul_comm, hx, mul_zero, neg_zero]

theorem key {e : R} {k K h h' a b : M} (hKk : K * k = 1) (hh : h' * h = 1)
    (hK : (1 - e) • (K - 1) = 0) (hhe : (1 - e) • (h - 1) = 0)
    (ha : (1 - k) * a = e • (1 : M)) (hb : b * (1 - h') = e • (1 : M)) :
    (K - 1) * (1 - (b - a) * (h - 1)) = h - 1 := by

  have hu : e • (K - 1) = K - 1 := by
    rw [sub_smul, one_smul, sub_eq_zero] at hK; exact hK.symm
  have hv : e • (h - 1) = h - 1 := by
    rw [sub_smul, one_smul, sub_eq_zero] at hhe; exact hhe.symm
  have hua : (K - 1) * a = e • K := by
    have hK1 : K - 1 = K * (1 - k) := by rw [mul_sub, mul_one, hKk]
    rw [hK1, mul_assoc, ha, mul_smul_comm, mul_one]
  have hbv : b * (h - 1) = e • h := by
    have hh1 : h - 1 = (1 - h') * h := by rw [sub_mul, one_mul, hh]
    rw [hh1, ← mul_assoc, hb, smul_mul_assoc, one_mul]
  calc (K - 1) * (1 - (b - a) * (h - 1))
      = (K - 1) - (K - 1) * (b * (h - 1)) + ((K - 1) * a) * (h - 1) := by noncomm_ring
    _ = (K - 1) - (e • (K - 1)) * h + K * (e • (h - 1)) := by
        rw [hbv, hua]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = h - 1 := by rw [hu, hv]; noncomm_ring

end Ring

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {β : Type} [Fintype β] [DecidableEq β]

theorem cayley (c : A →ₐ[R] A) {J k a : Matrix β β A} {e : R} (hk : kᵀ * J * k.map c = J) (hea : e • a = a)
    (ha : (1 - k) * a = e • (1 : Matrix β β A)) (he : e * e = e) : aᵀ * J + J * a.map c = e • J := by
  have hT : aᵀ * (1 - k)ᵀ = e • (1 : Matrix β β A) := by
    rw [← transpose_mul, ha, transpose_smul, transpose_one]
  have hac : (1 - k.map c) * a.map c = e • (1 : Matrix β β A) := by
    have h1 := congrArg c.mapMatrix ha
    rwa [map_mul, map_sub, map_one, map_smul, map_one, AlgHom.mapMatrix_apply,
      AlgHom.mapMatrix_apply] at h1
  have heac : e • a.map c = a.map c := by
    have h1 := congrArg c.mapMatrix hea
    rwa [map_smul, AlgHom.mapMatrix_apply] at h1
  have heaT : e • aᵀ = aᵀ := by rw [← transpose_smul, hea]

  have hid : (1 - k)ᵀ * J * (1 - k.map c) = (1 - k)ᵀ * J + J * (1 - k.map c) := by
    rw [transpose_sub, transpose_one]
    have e1 : (1 - kᵀ) * J * (1 - k.map c)
        = (1 - kᵀ) * J + J * (1 - k.map c) + (kᵀ * J * k.map c - J) := by noncomm_ring
    rw [e1, hk, sub_self, add_zero]
  have main : aᵀ * ((1 - k)ᵀ * J * (1 - k.map c)) * a.map c = e • J := by
    calc aᵀ * ((1 - k)ᵀ * J * (1 - k.map c)) * a.map c
        = (aᵀ * (1 - k)ᵀ) * J * ((1 - k.map c) * a.map c) := by simp only [Matrix.mul_assoc]
      _ = e • J := by
          rw [hT, hac, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.mul_one, smul_smul, he]
  have t1 : aᵀ * ((1 - k)ᵀ * J) * a.map c = J * a.map c := by
    rw [← Matrix.mul_assoc, hT, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul,
      ← Matrix.mul_smul, heac]
  have t2 : aᵀ * (J * (1 - k.map c)) * a.map c = aᵀ * J := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hac, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_smul, ← Matrix.smul_mul, heaT]
  rw [hid, Matrix.mul_add, Matrix.add_mul, t1, t2] at main
  rw [add_comm]
  exact main

def unip (N : Matrix β β A) : GL (β ⊕ β) A where
  val := fromBlocks (1 + N) (-N) N (1 - N)
  inv := fromBlocks (1 - N) N (-N) (1 + N)
  val_inv := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1 <;> noncomm_ring
  inv_val := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1 <;> noncomm_ring

theorem unip_mem (c : A →ₐ[R] A) {J N : Matrix β β A} (hN : Nᵀ * J + J * N.map c = 0) :
    unip N ∈ GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J) := by
  show ((unip N : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * GlobalTheory.WeilM.dbl J *
      ((unip N : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A).map c = GlobalTheory.WeilM.dbl J
  have hU : ((unip N : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) =
      fromBlocks (1 + N) (-N) N (1 - N) := rfl
  have hm1 : (1 + N).map c = 1 + N.map c := by
    have h := map_add c.mapMatrix 1 N
    rw [map_one] at h
    exact h
  have hm2 : (-N).map c = -N.map c := map_neg c.mapMatrix N
  have hm3 : (1 - N).map c = 1 - N.map c := by
    have h := map_sub c.mapMatrix 1 N
    rw [map_one] at h
    exact h
  rw [hU, GlobalTheory.WeilM.dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [transpose_add, transpose_sub, transpose_neg, transpose_one, hm1, hm2, hm3]

  refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · calc _ = J + (Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = J := by rw [hN, add_zero]
  · calc _ = -(Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = 0 := by rw [hN, neg_zero]
  · calc _ = -(Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = 0 := by rw [hN, neg_zero]
  · calc _ = -J + (Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = -J := by rw [hN, add_zero]

theorem cong_block {e : R} {x : Matrix β β A} (hx : (1 - e) • (x - 1) = 0) :
    (1 - e) • (fromBlocks x (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) - 1) = 0 := by
  have h1 : fromBlocks x (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) - 1 =
      fromBlocks (x - 1) 0 0 0 := by
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  rw [h1, fromBlocks_smul, hx]
  simp

theorem decomposition : ∀ (R A : Type) [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (c : A →ₐ[R] A) (β : Type) [inst_3 : Fintype β] [inst_4 : DecidableEq β] (J : Matrix β β A), IsUnit (Matrix.det J) →
    ∀ (e : R), e * e = e →
    ∀ (g k : ↥(GlobalTheory.WeilM.UG c J)), ((1 : R) - e) • ((↑(↑g : GL β A) : Matrix β β A) - (1 : Matrix β β A)) = (0 : Matrix β β A) →
    ((1 : R) - e) • ((↑(↑k : GL β A) : Matrix β β A) - (1 : Matrix β β A)) = (0 : Matrix β β A) →
    ∀ (a b : Matrix β β A), e • a = a →
    e • b = b →
    a * ((1 : Matrix β β A) - (↑(↑k : GL β A) : Matrix β β A)) = e • (1 : Matrix β β A) →
    ((1 : Matrix β β A) - (↑(↑k : GL β A) : Matrix β β A)) * a = e • (1 : Matrix β β A) →
    b * ((1 : Matrix β β A) - (↑(↑(g⁻¹ * k) : GL β A) : Matrix β β A)) = e • (1 : Matrix β β A) →
    ((1 : Matrix β β A) - (↑(↑(g⁻¹ * k) : GL β A) : Matrix β β A)) * b = e • (1 : Matrix β β A) →
    ∀ (gd kd : ↥(GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J))), (↑(↑gd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (↑(↑g : GL β A) : Matrix β β A) (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) →
    (↑(↑kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (↑(↑k : GL β A) : Matrix β β A) (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) →
    ∃ (p₁ : ↥(GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J))) (p₂ : ↥(GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J))) (t₁ : GL β A) (t₂ : GL β A), ((1 : R) - e) • ((↑(↑p₁ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - (1 : Matrix (β ⊕ β) (β ⊕ β) A)) = (0 : Matrix (β ⊕ β) (β ⊕ β) A) ∧
    ((1 : R) - e) • ((↑(↑p₂ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - (1 : Matrix (β ⊕ β) (β ⊕ β) A)) = (0 : Matrix (β ⊕ β) (β ⊕ β) A) ∧
    ((↑(↑p₁ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) : Matrix (β ⊕ β) β A) = ((GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) * (↑t₁ : Matrix β β A) : Matrix (β ⊕ β) β A) ∧
    ((↑(↑p₂ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) : Matrix (β ⊕ β) β A) = ((GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) * (↑t₂ : Matrix β β A) : Matrix (β ⊕ β) β A) ∧
    gd = kd * p₁ * kd⁻¹ * p₂ := by
  intro R A _ _ _ c β _ _ J _ e he g k hg hk a b hea heb hak hka hbh hhb gd kd hgd hkd
  obtain ⟨Km, hKm⟩ : ∃ Km : Matrix β β A, Km = (((k : GL β A)⁻¹ : GL β A) : Matrix β β A) :=
    ⟨_, rfl⟩
  obtain ⟨gi, hgi⟩ : ∃ gi : Matrix β β A, gi = (((g : GL β A)⁻¹ : GL β A) : Matrix β β A) :=
    ⟨_, rfl⟩
  have hKk : Km * ((k : GL β A) : Matrix β β A) = 1 := by rw [hKm]; exact Units.inv_mul _
  have hkK : ((k : GL β A) : Matrix β β A) * Km = 1 := by rw [hKm]; exact Units.mul_inv _
  have hgig : gi * ((g : GL β A) : Matrix β β A) = 1 := by rw [hgi]; exact Units.inv_mul _
  have hggi : ((g : GL β A) : Matrix β β A) * gi = 1 := by rw [hgi]; exact Units.mul_inv _
  have hhgk : (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A) = gi * ((k : GL β A) : Matrix β β A) := by rw [hgi]; rfl

  have hh : (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A) * (Km * ((g : GL β A) : Matrix β β A)) = 1 := by
    rw [hhgk, Matrix.mul_assoc, ← Matrix.mul_assoc ((k : GL β A) : Matrix β β A) Km, hkK, Matrix.one_mul, hgig]
  have hh2 : Km * ((g : GL β A) : Matrix β β A) * (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A) = 1 := by
    rw [hhgk, Matrix.mul_assoc, ← Matrix.mul_assoc ((g : GL β A) : Matrix β β A) gi, hggi, Matrix.one_mul, hKk]
  have hKc : (1 - e) • (Km - 1) = 0 := cong_inv hk hKk
  have hhc : (1 - e) • (Km * ((g : GL β A) : Matrix β β A) - 1) = 0 := cong_mul hKc hg
  have key1 := key hKk hh hKc hhc hka hbh
  have key2 := key hh2 hkK hhc hKc hhb hak

  have hca := cayley c (J := J) (k := ((k : GL β A) : Matrix β β A)) (a := a) k.2 hea hka he
  have hcb := cayley c (J := J) (k := (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A)) (a := b) (g⁻¹ * k).2 heb hhb he
  have hskew : (a - b)ᵀ * J + J * (a - b).map c = 0 := by
    have hmap : (a - b).map c = a.map c - b.map c := by ext i j; simp
    rw [transpose_sub, hmap, Matrix.sub_mul, Matrix.mul_sub]
    calc aᵀ * J - bᵀ * J + (J * a.map c - J * b.map c)
        = (aᵀ * J + J * a.map c) - (bᵀ * J + J * b.map c) := by abel
      _ = 0 := by rw [hca, hcb, sub_self]
  obtain ⟨u, hu⟩ : ∃ u : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J),
      ((u : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks (1 + (a - b)) (-(a - b)) (a - b) (1 - (a - b)) ∧
      (((u⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks (1 - (a - b)) (a - b) (-(a - b)) (1 + (a - b)) :=
    ⟨⟨unip (a - b), unip_mem c hskew⟩, rfl, rfl⟩
  have h2 : (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * ((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = 1 := Units.inv_mul _
  have hkdinv : (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks Km 0 0 1 := by
    have h1 : ((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks Km 0 0 1 = 1 := by
      rw [hkd, fromBlocks_multiply, hkK]; simp [fromBlocks_one]
    calc (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks Km 0 0 1) := by rw [h1, Matrix.mul_one]
      _ = fromBlocks Km 0 0 1 := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hblk : ∀ P Q S T : Matrix β β A,
      fromBlocks P Q S T - 1 = fromBlocks (P - 1) Q S (T - 1) := by
    intro P Q S T
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  have hN0 : (1 - e) • (a - b) = 0 := by simp [smul_sub, sub_smul, hea, heb]
  have hN0' : (1 - e) • (b - a) = 0 := by simp [smul_sub, sub_smul, hea, heb]
  have hkdc : (1 - e) • (((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := by rw [hkd]; exact cong_block hk
  have hgdc : (1 - e) • (((gd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := by rw [hgd]; exact cong_block hg
  have hkdic : (1 - e) • ((((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := cong_inv hkdc h2
  have huc : (1 - e) • (((u : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := by
    rw [hu.1, hblk, fromBlocks_smul]; simp [hN0, hN0']

  have ht : (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) * (1 - (a - b) * (Km - 1)) = 1 := by
    have e1 : (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) * (1 - (a - b) * (Km - 1)) =
        (1 - (a - b) * (Km - 1)) - (b - a) * ((Km * ((g : GL β A) : Matrix β β A) - 1) * (1 - (a - b) * (Km - 1))) := by
      noncomm_ring
    rw [e1, key2]
    noncomm_ring
  have hK2 : Km * (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) = (1 + (a - b)) * (Km * ((g : GL β A) : Matrix β β A)) - (a - b) := by
    have e1 : Km * (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) =
        (Km - 1) * (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) + (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) := by
      noncomm_ring
    rw [e1, key1]
    noncomm_ring
  have hfin : ((k : GL β A) : Matrix β β A) * ((1 + (a - b)) * (Km * ((g : GL β A) : Matrix β β A)) - (a - b)) = 1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1) := by
    rw [← hK2, ← Matrix.mul_assoc, hkK, Matrix.one_mul]
  have hv : (((kd * u * kd⁻¹ * gd : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) :
      Matrix (β ⊕ β) (β ⊕ β) A) = ((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * ((u : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * ((gd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) := rfl
  refine ⟨u⁻¹, kd * u * kd⁻¹ * gd, 1,
    ⟨1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1), 1 - (a - b) * (Km - 1), ht, mul_eq_one_comm.mp ht⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu.2, hblk, fromBlocks_smul]; simp [hN0, hN0']
  · rw [hv]; exact cong_mul (cong_mul (cong_mul hkdc huc) hkdic) hgdc
  · rw [hu.2, GlobalTheory.WeilM.diagCols]
    simp only [fromBlocks_mul_fromRows, fromRows_mul, Units.val_one, Matrix.mul_one,
      Matrix.one_mul]
    rw [fromRows_ext_iff]
    constructor <;> abel
  · rw [hv, hkd, hu.1, hkdinv, hgd, GlobalTheory.WeilM.diagCols]
    simp only [Matrix.mul_assoc, fromBlocks_mul_fromRows, fromRows_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Units.val_mk]
    rw [fromRows_ext_iff]
    constructor
    · refine Eq.trans ?_ (hfin.trans ?_) <;> noncomm_ring
    · noncomm_ring
  · group

end GlobalTheory.UnipotentCongruenceInverse
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesTangentLiftNeZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

noncomputable section

theorem _root_.GlobalTheory.CompHS.det_tanLift_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K}
    (hz : z ≫ toFlag M = X.ptY Q) {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame (psiSet H) Q v) {zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)}
    (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) (i : M.K.bundle.ι) (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hzO : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hJ : evalPt z O hzO (M.K.jacobian i hO g) ≠ 0), (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det ≠ 0 := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS K _ _ z ho Q hz v hv zv hl i O hO g hzO hzv hJ
  obtain ⟨O₁, hzO₁, x, w, hw, hdx⟩ := GlobalTheory.T.exists_tangentVectors_functions_invertible_derivs M.str (dimFlag Dw) z
  have hzi : ⊤ ≤ z ⁻¹ᵁ M.K.bundle.U i := fun s hs => hO (hzO hs)
  have hzO' : ⊤ ≤ z ⁻¹ᵁ (O₁ ⊓ M.K.bundle.U i) := fun s hs => ⟨hzO₁ hs, hzi hs⟩
  let x' : Fin (dimFlag Dw) → Γ(M.X, O₁ ⊓ M.K.bundle.U i) := fun a => resG M.X inf_le_left (x a)
  have hwO : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O := fun b => le_preimage_of_dualNumber _ _ _ (by rw [hw b]; exact hzO)
  have hwO' : ∀ b, ⊤ ≤ w b ⁻¹ᵁ (O₁ ⊓ M.K.bundle.U i) := fun b => le_preimage_of_dualNumber _ _ _ (by rw [hw b]; exact hzO')
  have hwO₁ : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O₁ := fun b => le_preimage_of_dualNumber _ _ _ (by rw [hw b]; exact hzO₁)
  have e1 : (Matrix.of fun a b => (evalPt (w b) (O₁ ⊓ M.K.bundle.U i) (hwO' b) (x' a)).snd) =
      Matrix.of fun a b => (evalPt (w b) O₁ (hwO₁ b) (x a)).snd := by
    ext a b
    simp only [Matrix.of_apply, x']
    rw [evalPt_res (w b) inf_le_left (hwO₁ b) (hwO' b)]
  have hjc := GlobalTheory.T.det_derivatives_div_jacobian_independent M z i w hw O (O₁ ⊓ M.K.bundle.U i) hO inf_le_right g x' hzO hzO' hwO hwO'
  rw [e1] at hjc
  have hdg : (Matrix.of fun a b => (evalPt (w b) O (hwO b) (g a)).snd).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hjc
    exact mul_ne_zero (hdx hwO₁) hJ hjc.symm
  have hQ := hKS K Q
  have hspan : ∀ c0 : Fin (dimFlag Dw), ∃ C : TIx Dw (psiSet H) → K, ∀ a,
      (evalPt (w c0) O (hwO c0) (g a)).snd = ∑ t, C t * (evalPt (zv t) O (hzv t) (g a)).snd := by
    intro c0
    obtain ⟨wf, hdef, hlw⟩ := GlobalTheory.T.exists_dualNumber_deformation_lift_modification M z ho hz (w c0) (hw c0)
    obtain ⟨Mx, hMx, -⟩ := hQ.existsUnique hdef.isTanX
    obtain ⟨C, hC⟩ := GlobalTheory.T.derivative_along_kodairaSpencer_deformation_lift M z ho hQ hz hv hl hdef hMx hlw
    refine ⟨Sum.elim Mx C, fun a => ?_⟩
    rw [hC O (g a) (hwO c0) hzv, Fintype.sum_sum_type]
    rfl
  choose C hC using hspan
  have hmat : (Matrix.of fun a b => (evalPt (w b) O (hwO b) (g a)).snd) =
      (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd) *
        Matrix.of (fun b c0 => C c0 (tanOrd Dw b)) := by
    ext a c0
    rw [Matrix.mul_apply, Matrix.of_apply, hC c0 a, ← Equiv.sum_comp (tanOrd Dw)]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Matrix.of_apply]
    ring
  intro h0
  apply hdg
  rw [hmat, Matrix.det_mul, h0, zero_mul]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetPowSectionRationalGenericPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detPowSection_rational_genericPoint : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ (m : ℕ) (σ : (lbPow (det W r) m).Sec), σ ≠ 0 → ∃ f : K, f ≠ 0 ∧ ∀ (v : Place k K) (g : Matrix (Fin r) (Fin r) K), LocFrame x s v g → v.1 (f * g.det ^ m) ≤ 1 ∧ ∀ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x → b (IsLocalRing.closedPoint v.O) ∉ Out.nonzeroLocus σ → v.1 (f * g.det ^ m) < 1 := by
  first | exact @GlobalTheory.Nef.sec_detPow_rational | exact GlobalTheory.Nef.sec_detPow_rational | (intros; apply GlobalTheory.Nef.sec_detPow_rational <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
section
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)

noncomputable section

namespace GlobalTheory.DiffCoprimeP

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem not_le_differentIdeal_of_psiUnr {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (v : Pl F) (hu : PsiUnr ψ v) : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := by
  classical
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ)

  have key : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔
      Valued.v x ≤ exp (-FractionalIdeal.count F v (codiff F)) := by
    intro x
    set α : Af F := GlobalTheory.AdelicU.singleFin v x with hα
    have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
    have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
    have k1 : (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔
        ∀ β : Af F, (∀ w, β w ∈ w.adicCompletionIntegers F) → ψ (pairA F 0 (β * α)) = 1 := by
      constructor
      · intro H β hβ
        have e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v) := by
          apply GlobalTheory.AdelicU.af_ext
          intro u
          by_cases hu : u = v
          · subst hu
            rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
            change β u * x = x * β u
            ring
          · rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
        rw [e]
        exact H _ (hβ v)
      · intro H y hy
        have e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y) := by
          rw [hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]
        have := H (GlobalTheory.AdelicU.singleFin v y) (fun w => by
          by_cases hw : w = v
          · subst hw
            change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _
            rw [GlobalTheory.AdelicU.evalV_singleFin_self]
            exact hy
          · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _
            rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
            exact zero_mem _)
        rw [e] at this
        exact this
    rw [k1, ← h, mem_adelicIdeal_iff codiff_ne_zero]
    constructor
    · intro H
      have := H v
      rwa [hαv] at this
    · intro H w
      by_cases hw : w = v
      · subst hw
        rw [hαv]
        exact H
      · rw [hαw w hw, map_zero]
        exact zero_le
  set c := FractionalIdeal.count F v (codiff F) with hc

  have hc0 : c ≤ 0 := by
    have := FractionalIdeal.count_mono F v (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
      (one_le_codiff (F := F))
    rw [FractionalIdeal.count_one] at this
    omega

  have hc1 : 0 ≤ c := by
    by_contra hneg
    push_neg at hneg
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact exp_ne_zero hπ.symm
    set x : Fv F v := ((π⁻¹ : F) : v.adicCompletion F) with hx
    have hvx : Valued.v x = exp 1 := by
      rw [hx, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ, ← exp_neg, neg_neg]
    have h1 : Valued.v x ≤ exp (-c) := by
      rw [hvx, exp_le_exp]
      omega
    have h2 := (hu x).1 ((key x).2 h1)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hvx, ← exp_zero, exp_le_exp] at h2
    omega
  have hc2 : c = 0 := le_antisymm hc0 hc1
  intro hle
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have h0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have h1 := FractionalIdeal.count_coe F v h0
  rw [hD, FractionalIdeal.count_inv, ← hc, hc2, neg_zero] at h1
  have h2 := (Associates.count_ne_zero_iff_dvd h0 v.irreducible).2 (Ideal.dvd_iff_le.2 hle)
  exact h2 (by exact_mod_cast h1.symm)

theorem count_diffE_eq_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ v ∈ B.P, ∀ w : HeightOneSpectrum (𝓞 E),
      w.under (𝓞 F) = v → FractionalIdeal.count E w (diffE E) = 0 := by
  intro F E _ _ _ _ _ σ B hB v hv w hw
  have hnF := not_le_differentIdeal_of_psiUnr hB.std v (hB.psiP v hv)
  haveI := hB.unram
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := inferInstance
  have hEq : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
      (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu, Ideal.top_mul]
  have h0 : differentIdeal ℤ (𝓞 E) ≠ 0 := differentIdeal_ne_bot
  unfold diffE
  rw [FractionalIdeal.count_coe E w h0]
  have hnd : ¬ w.asIdeal ∣ differentIdeal ℤ (𝓞 E) := by
    intro hd
    apply hnF
    rw [hEq, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at hd
    rw [← hw]
    exact hd
  rw [not_not.1 (mt (Associates.count_ne_zero_iff_dvd h0 w.irreducible).1 hnd)]
  rfl

end GlobalTheory.DiffCoprimeP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_intertwiner_good_models : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  first | exact @GlobalTheory.EvAdm.comp_mem_adm | exact GlobalTheory.EvAdm.comp_mem_adm | (intros; apply GlobalTheory.EvAdm.comp_mem_adm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_selfDualLattice_indicator_is_vacuum : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
    ∀ᶠ v in Filter.cofinite, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v
      (Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  first | exact @GlobalTheory.VacIndic.eventually_isVac_indicator | exact GlobalTheory.VacIndic.eventually_isVac_indicator | (intros; apply GlobalTheory.VacIndic.eventually_isVac_indicator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSchemeRepresentingEtaleLevelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtaleScheme_representing_etaleLevels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Scheme.{0}) (π : Y ⟶ S) (lu : D.La → (Over.mk π ⟶ o.A)), IsFinite π ∧ Etale π ∧ IsEtLevOver o w0 r lu ∧ ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), IsEtLevOver o w0 r l → ∃! f : T ⟶ Over.mk π, ∀ y, f ≫ lu y = l y := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.exists_etLevScheme) | (exact GlobalTheory.UPel.HT.EtLev.exists_etLevScheme) | (intros; apply GlobalTheory.UPel.HT.EtLev.exists_etLevScheme <;> assumption)
end

