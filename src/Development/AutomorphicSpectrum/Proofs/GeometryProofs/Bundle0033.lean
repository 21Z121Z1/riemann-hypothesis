import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatrixChartRatios
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem det_mul_eq_sum {R : Type*} [CommRing R] {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p]
    [DecidableEq p] (A : Matrix m p R) (C : Matrix p m R) :
    (A * C).det = ∑ f : m → p, (∏ i, A i (f i)) * (C.submatrix f id).det := by
  have h : (A * C) = fun i => ∑ j, A i j • C j := by
    ext i k
    simp [Matrix.mul_apply, Finset.sum_apply]
  calc (A * C).det = Matrix.detRowAlternating (fun i => ∑ j, A i j • C j) := by rw [h]; rfl
    _ = ∑ f : m → p, Matrix.detRowAlternating (fun i => A i (f i) • C (f i)) :=
        (Matrix.detRowAlternating (n := m) (R := R)).toMultilinearMap.map_sum _
    _ = _ := by
        refine Finset.sum_congr rfl fun f _ => ?_
        have := (Matrix.detRowAlternating (n := m) (R := R)).toMultilinearMap.map_smul_univ
          (fun i => A i (f i)) (fun i => C (f i))
        exact this.trans (by rw [smul_eq_mul]; rfl)

theorem adjoin_int_mem {K : Type*} [Field K] (L : Subfield K) {t : Set K} (ht : ∀ a ∈ t, a ∈ L) {g : K}
    (hg : g ∈ Algebra.adjoin ℤ t) : g ∈ L := by
  induction hg using Algebra.adjoin_induction with
  | mem a ha => exact ht a ha
  | algebraMap n => simpa using intCast_mem L n
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem exists_div_of_mem_closure {K : Type*} [Field K] [Algebra ℤ K] {t : Set K} {a : K} (ha : a ∈ Subfield.closure t) :
    ∃ g ∈ Algebra.adjoin ℤ t, ∃ h ∈ Algebra.adjoin ℤ t, h ≠ 0 ∧ a = g / h := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.1 ha
  have key : ∀ w ∈ Subring.closure t, w ∈ Algebra.adjoin ℤ t := by
    intro w hw
    induction hw using Subring.closure_induction with
    | mem a ha => exact Algebra.subset_adjoin ha
    | zero => exact zero_mem _
    | one => exact one_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | neg a _ ha => exact neg_mem ha
    | mul a b _ _ ha hb => exact mul_mem ha hb
  by_cases h0 : z = 0
  · exact ⟨0, zero_mem _, 1, one_mem _, one_ne_zero, by simp [h0]⟩
  · exact ⟨y, key y hy, z, key z hz, h0, rfl⟩

variable {Ω : Type} [Field Ω] {S : Type} {r : S → ℕ}

theorem genU_of_lt (s : S) {l k : Fin (r s)} (h : l < k) : genU Ω r s l k = 0 := by
  have h1 : ¬ k < l := not_lt.2 h.le
  simp [genU, h1, h.ne]

theorem genU_self (s : S) (k : Fin (r s)) : genU Ω r s k k = 1 := by
  simp [genU]

theorem det_genU_rows (s : S) (k l : Fin (r s)) (hkl : k ≤ l) :
    ((genU Ω r s).submatrix
      (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then l else Fin.castLE k.2 i) (Fin.castLE k.2)).det
      = genU Ω r s l k := by
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_castSucc]
    have h1 : ∀ i : Fin (k : ℕ), (genU Ω r s).submatrix
        (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then l else Fin.castLE k.2 i) (Fin.castLE k.2)
        i.castSucc i.castSucc = 1 := by
      intro i
      have : ((i.castSucc : Fin ((k : ℕ) + 1)) : ℕ) ≠ k := by simpa using i.2.ne
      simp only [Matrix.submatrix_apply, if_neg this]
      exact genU_self s _
    simp only [h1, Finset.prod_const_one, one_mul, Matrix.submatrix_apply, Fin.val_last, if_true]
    congr 1
  · intro i j hij
    have hij' : i < j := hij
    have hi : (i : ℕ) ≠ k := by
      have := j.2
      have : (i : ℕ) < j := hij'
      omega
    simp only [Matrix.submatrix_apply, if_neg hi]
    exact genU_of_lt s (show Fin.castLE k.2 i < Fin.castLE k.2 j from hij')

variable {E : Type} [AddCommGroup E] [Module Ω E] {n : S → ℕ}

theorem map_mul_flagMat (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S)
    (B : Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : B * Matrix.of (fun j l => φ s j (c s l)) = 1) :
    B.map (algebraMap Ω (GenField Ω r)) * flagMat φ c s = genU Ω r s := by
  have h : Matrix.of (fun j l => algebraMap Ω (GenField Ω r) (φ s j (c s l))) =
      (Matrix.of (fun j l => φ s j (c s l))).map (algebraMap Ω (GenField Ω r)) := by
    ext j l
    simp
  rw [flagMat, h, ← Matrix.mul_assoc, ← Matrix.map_mul, hB]
  simp

theorem det_genU_submatrix (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S)
    (B : Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : B * Matrix.of (fun j l => φ s j (c s l)) = 1) {d : ℕ} (hd : d ≤ r s)
    (R : Fin d → Fin (r s)) :
    ((genU Ω r s).submatrix R (Fin.castLE hd)).det =
      ∑ f : Fin d → Fin (n s), (∏ i, algebraMap Ω (GenField Ω r) (B (R i) (f i))) *
        ((flagMat φ c s).submatrix f (Fin.castLE hd)).det := by
  classical
  have h : (genU Ω r s).submatrix R (Fin.castLE hd) =
      ((B.map (algebraMap Ω (GenField Ω r))).submatrix R id) *
        ((flagMat φ c s).submatrix id (Fin.castLE hd)) := by
    rw [← map_mul_flagMat φ c s B hB]
    ext i j
    simp [Matrix.mul_apply]
  rw [h, det_mul_eq_sum]
  simp [Matrix.submatrix_submatrix]

theorem ratio_update {Q : Type*} [Fintype Q] [DecidableEq Q] {T : Q → Type*} {K : Type*} [Field K]
    (D : ∀ q, T q → K) (ρ : ∀ q, T q) (hρ : ∀ q, D q (ρ q) ≠ 0) (q : Q) (f : T q) (a : K) (ha : a ≠ 0) :
    (a * ∏ q', D q' (Function.update ρ q f q')) / (a * ∏ q', D q' (ρ q')) = D q f / D q (ρ q) := by
  have hP : (∏ q' ∈ Finset.univ.erase q, D q' (ρ q')) ≠ 0 := Finset.prod_ne_zero_iff.2 fun q _ => hρ q
  rw [mul_div_mul_left _ _ ha, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q),
    ← Finset.mul_prod_erase Finset.univ (fun q' => D q' (ρ q')) (Finset.mem_univ q),
    Function.update_self,
    Finset.prod_congr rfl (g := fun q' => D q' (ρ q'))
      (fun q' hq' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hq')])]
  exact mul_div_mul_right _ _ hP

theorem exists_minor_ne_zero (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S)
    (B : Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : B * Matrix.of (fun j l => φ s j (c s l)) = 1) (k : Fin (r s)) :
    ∃ f : Fin ((k : ℕ) + 1) → Fin (n s), ((flagMat φ c s).submatrix f (Fin.castLE k.2)).det ≠ 0 := by
  by_contra hall
  push_neg at hall
  have h1 := det_genU_submatrix φ c s B hB k.2
    (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then k else Fin.castLE k.2 i)
  rw [det_genU_rows s k k le_rfl, genU_self, Finset.sum_eq_zero (fun f _ => by rw [hall f, mul_zero])] at h1
  exact one_ne_zero h1

theorem genU_mem (L : Subfield (GenField Ω r)) (hbase : ∀ b : Ω, algebraMap Ω (GenField Ω r) b ∈ L)
    (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S)
    (B : Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : B * Matrix.of (fun j l => φ s j (c s l)) = 1) (k l : Fin (r s)) (hkl : k ≤ l)
    (ρ : Fin ((k : ℕ) + 1) → Fin (n s)) (hρ : ((flagMat φ c s).submatrix ρ (Fin.castLE k.2)).det ≠ 0)
    (hminor : ∀ f : Fin ((k : ℕ) + 1) → Fin (n s), ((flagMat φ c s).submatrix f (Fin.castLE k.2)).det /
        ((flagMat φ c s).submatrix ρ (Fin.castLE k.2)).det ∈ L) :
    genU Ω r s l k ∈ L := by
  have hrows : ∀ R : Fin ((k : ℕ) + 1) → Fin (r s),
      ((genU Ω r s).submatrix R (Fin.castLE k.2)).det /
        ((flagMat φ c s).submatrix ρ (Fin.castLE k.2)).det ∈ L := by
    intro R
    rw [det_genU_submatrix φ c s B hB k.2 R, Finset.sum_div]
    refine sum_mem fun f _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (prod_mem fun i _ => hbase _) (hminor f)
  have h1 := hrows (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then l else Fin.castLE k.2 i)
  rw [det_genU_rows s k l hkl] at h1
  have h0 := hrows (fun i : Fin ((k : ℕ) + 1) => if (i : ℕ) = k then k else Fin.castLE k.2 i)
  rw [det_genU_rows s k k le_rfl, genU_self] at h0
  have := div_mem h1 h0
  rwa [div_div_div_cancel_right₀ hρ, div_one] at this

theorem mem_of_genU_mem (L : Subfield (GenField Ω r)) (hbase : ∀ b : Ω, algebraMap Ω (GenField Ω r) b ∈ L)
    (hentry : ∀ (s : S) (k l : Fin (r s)), k ≤ l → genU Ω r s l k ∈ L) (a : GenField Ω r) : a ∈ L := by
  have hpoly : ∀ p : MvPolynomial (GenIx r) Ω,
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) p ∈ L := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C b =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact hbase b
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      obtain ⟨s, ⟨⟨l, k⟩, h⟩⟩ := i
      have := hentry s k l (le_of_lt h)
      rwa [genU, dif_pos h] at this
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (GenIx r) Ω) a
  exact div_mem (hpoly p) (hpoly q)

theorem base_mem (L : Subfield (GenField Ω r)) {κ : Type} (x : κ → Ω) (c₀ : κ)
    (hΩ : ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h)
    (hgen : ∀ j, algebraMap Ω (GenField Ω r) (x j / x c₀) ∈ L) (b : Ω) :
    algebraMap Ω (GenField Ω r) b ∈ L := by
  have hgen' : ∀ b ∈ (Set.range fun j => x j / x c₀), b ∈ L.comap (algebraMap Ω (GenField Ω r)) := by
    rintro _ ⟨j, rfl⟩
    exact hgen j
  obtain ⟨g, hg, h, hh, -, rfl⟩ := hΩ b
  exact div_mem (adjoin_int_mem _ hgen' hg) (adjoin_int_mem _ hgen' hh)

theorem mem_of_ratio_mem [Fintype S] (κ : Type) (x : κ → Ω) (φ : ∀ s, Fin (n s) → Module.Dual Ω E)
    (c : ∀ s, Fin (r s) → E) (c₀ : κ) (hx0 : x c₀ ≠ 0)
    (hΩ : ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h)
    (B : ∀ s, Matrix (Fin (r s)) (Fin (n s)) Ω)
    (hB : ∀ s, B s * Matrix.of (fun j l => φ s j (c s l)) = 1)
    (ρ : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
    (hρ : ∀ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (ρ q) (Fin.castLE q.2.2)).det ≠ 0)
    (L : Subfield (GenField Ω r))
    (hratio : ∀ j : FlagIx κ n r, flagCoord κ x φ c j / flagCoord κ x φ c (c₀, ρ) ∈ L)
    (a : GenField Ω r) : a ∈ L := by
  classical
  have hxK : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 :=
    (map_ne_zero (algebraMap Ω (GenField Ω r))).2 hx0
  have hP : (∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (ρ q) (Fin.castLE q.2.2)).det) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun q _ => hρ q
  have hbase : ∀ b : Ω, algebraMap Ω (GenField Ω r) b ∈ L := by
    refine base_mem L x c₀ hΩ fun j => ?_
    have h := hratio (j, ρ)
    have e : flagCoord κ x φ c (j, ρ) / flagCoord κ x φ c (c₀, ρ) =
        algebraMap Ω (GenField Ω r) (x j / x c₀) := by
      rw [map_div₀]
      exact mul_div_mul_right _ _ hP
    rwa [e] at h
  have hminor : ∀ (q : Σ s, Fin (r s)) (f : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      ((flagMat φ c q.1).submatrix f (Fin.castLE q.2.2)).det /
        ((flagMat φ c q.1).submatrix (ρ q) (Fin.castLE q.2.2)).det ∈ L := by
    intro q f
    have h := hratio (c₀, Function.update ρ q f)
    have e := ratio_update (fun (q : Σ s, Fin (r s)) (g : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) =>
      ((flagMat φ c q.1).submatrix g (Fin.castLE q.2.2)).det) ρ hρ q f _ hxK
    exact e ▸ h
  exact mem_of_genU_mem L hbase (fun s k l hkl => genU_mem L hbase φ c s (B s) (hB s) k l hkl (ρ ⟨s, k⟩)
    (hρ ⟨s, k⟩) (hminor ⟨s, k⟩)) a

theorem flagCoord_generate (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) [Fintype S]
    (r n : S → ℕ) (κ : Type) (x : κ → Ω) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (c₀ : κ)
    (hx0 : x c₀ ≠ 0)
    (hΩ : ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h)
    (hB : ∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (c s l)) = 1) :
    ∃ J₀ : FlagIx κ n r, flagCoord κ x φ c J₀ ≠ 0 ∧ ∀ a : GenField Ω r,
      ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀),
        h ≠ 0 ∧ a = g / h := by
  classical
  choose B hB using hB
  have hne : ∀ q : (Σ s, Fin (r s)), ∃ f : Fin ((q.2 : ℕ) + 1) → Fin (n q.1),
      ((flagMat φ c q.1).submatrix f (Fin.castLE q.2.2)).det ≠ 0 :=
    fun q => exists_minor_ne_zero φ c q.1 (B q.1) (hB q.1) q.2
  choose ρ hρ using hne
  have hF0 : flagCoord κ x φ c (c₀, ρ) ≠ 0 :=
    mul_ne_zero ((map_ne_zero (algebraMap Ω (GenField Ω r))).2 hx0)
      (Finset.prod_ne_zero_iff.2 fun q _ => hρ q)
  refine ⟨(c₀, ρ), hF0, fun a => ?_⟩
  apply exists_div_of_mem_closure
  exact mem_of_ratio_mem κ x φ c c₀ hx0 hΩ B hB ρ hρ (Subfield.closure _)
    (fun j => Subfield.subset_closure (Set.mem_range_self j)) a

end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameViaTwistedGenerators
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

theorem regAt_generic_eq_top {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hg : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨s, hs⟩ := hg.bij.2 a
  refine (RingHom.mem_range).2 ⟨s, ?_⟩
  show (X.presheaf.stalkSpecializes (specializes_refl (genPt ξ)) ≫ Scheme.stalkClosedPointTo ξ).hom s = a
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact hs

theorem exists_leftInverse_flagForms (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (r : ℕ)
    (V : Submodule Ω E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (c : Fin r → E)
    (hT : CoordTie ℤ ξ x) (hV : L.IsVB r V) (hG : IsTwistGen ξ x L m φ)
    (hc : LinearIndependent Ω c) (hs : Submodule.span Ω (Set.range c) = V) :
    ∃ B : Matrix (Fin r) (Fin n) Ω, B * Matrix.of (fun j l => φ j (c l)) = 1 := by
  let p₀ : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  have hreg : ∀ a : Ω, a ∈ regAt ξ p₀ := fun a => regAt_generic_eq_top hT.gen a
  obtain ⟨k, hk⟩ := hT.cover p₀
  unfold Lat.IsVB Lat.IsVBOn at hV
  obtain ⟨U, hU, b, hbV, hbF⟩ := hV p₀ (Set.mem_univ _)
  obtain ⟨-, hLp⟩ := hbF p₀ (Set.mem_univ _) hU
  obtain ⟨-, hG2⟩ := hG
  have hw0 : ∀ i : Fin r, ∃ w : Module.Dual Ω E, ∀ l, w (c l) = if i = l then 1 else 0 := by
    intro i
    obtain ⟨w, hwf⟩ := LinearMap.exists_extend ((Module.Basis.span hc).coord i)
    refine ⟨w, fun l => ?_⟩
    have h1 : w (c l) = (Module.Basis.span hc).coord i (Module.Basis.span hc l) := by
      rw [← hwf]
      simp [Module.Basis.span_apply]
    rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = l
    · subst h
      simp
    · simp [h, Ne.symm h]
  choose w hw using hw0
  have hg0 : ∀ i, ∃ g : Fin n → Ω, (∀ j, g j ∈ regAt ξ p₀) ∧
      ∀ e ∈ L p₀, w i e = ∑ j, g j * (φ j e / x k ^ m) :=
    fun i => hG2 p₀ k hk (w i) (fun e _ => hreg _)
  choose g hgr hg using hg0
  have key : ∀ i, ∀ e ∈ V, w i e = ∑ j, g i j / x k ^ m * φ j e := by
    intro i
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : E →ₗ[Ω] Ω, ψ = ∑ j, (g i j / x k ^ m) • φ j := ⟨_, rfl⟩
    have hψ : ∀ e, ψ e = ∑ j, g i j / x k ^ m * φ j e := by
      intro e
      rw [hψdef]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have heq : Set.EqOn (w i) ψ (Set.range b) := by
      rintro _ ⟨t, rfl⟩
      have hbt : b t ∈ L p₀ := by
        rw [hLp]
        exact Submodule.subset_span ⟨t, rfl⟩
      rw [hg i (b t) hbt, hψ]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    intro e he
    rw [← hbV] at he
    rw [LinearMap.eqOn_span' heq he, hψ]
  refine ⟨Matrix.of fun i j => g i j / x k ^ m, ?_⟩
  ext i l
  have hcl : c l ∈ V := by
    rw [← hs]
    exact Submodule.subset_span ⟨l, rfl⟩
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [← key i (c l) hcl, hw i l]

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGenerators
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart

theorem exists_eq_div_adjoin (X : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ)
    (hT : CoordTie ℤ ξ x) (hc : x c ≠ 0) (a : Ω) :
    ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), h ≠ 0 ∧ a = g / h := by
  obtain ⟨U, hU, hUc⟩ := hT.affine c hc
  have hreg0 : ∀ b : Ω, b ∈ regAt ξ ⟨genPt ξ, specializes_refl _⟩ := by
    intro b
    obtain ⟨s, hs⟩ := hT.gen.bij.2 b
    show b ∈ (genMap ξ _).range
    refine RingHom.mem_range.mpr ⟨s, ?_⟩
    simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    first
      | exact hs
      | (rw [Category.id_comp]; exact hs)
      | simpa using hs
  have hgU : genPt ξ ∈ U :=
    (hUc (genPt ξ)).mpr ⟨specializes_refl _, And.intro hc fun _ => hreg0 _⟩
  let φ : Γ(X, U) →+* Ω := (X.presheaf.germ U (genPt ξ) hgU ≫ Scheme.stalkClosedPointTo ξ).hom
  have key : ∀ r : Γ(X, U), φ r ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    intro r
    refine (hT.ring c hc (φ r)).mpr fun p hp => ?_
    have hpU : p.1 ∈ U := (hUc p.1).mpr ⟨p.2, hp⟩
    show φ r ∈ (genMap ξ p).range
    refine RingHom.mem_range.mpr ⟨(X.presheaf.germ U p.1 hpU).hom r, ?_⟩
    have e0 : X.presheaf.germ U p.1 hpU ≫ X.presheaf.stalkSpecializes p.2 =
        X.presheaf.germ U (genPt ξ) hgU := by
      first
        | simp
        | exact TopCat.Presheaf.germ_stalkSpecializes X.presheaf hpU p.2
        | exact TopCat.Presheaf.germ_stalkSpecializes hpU p.2
    show (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ).hom
        ((X.presheaf.germ U p.1 hpU).hom r) = φ r
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
    first
      | exact congrArg (fun (m : Γ(X, U) ⟶ CommRingCat.of Ω) => CommRingCat.Hom.hom m r)
          ((reassoc_of% e0) (Scheme.stalkClosedPointTo ξ))
      | (simp only [reassoc_of% e0]; rfl)
  have gres : ∀ {W W' : X.Opens} (hle : W ≤ W') (hw : genPt ξ ∈ W) (z : Γ(X, W')),
      (X.presheaf.germ W (genPt ξ) hw).hom ((X.presheaf.map (homOfLE hle).op).hom z) =
        (X.presheaf.germ W' (genPt ξ) (hle hw)).hom z := by
    intro W W' hle hw z
    have e : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ W (genPt ξ) hw =
        X.presheaf.germ W' (genPt ξ) (hle hw) := by
      first
        | simp
        | exact TopCat.Presheaf.germ_res _ _ _ _
    exact congrArg (fun m => m.hom z) e
  obtain ⟨s0, hs0⟩ : ∃ s0 : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom s0 = a :=
    hT.gen.bij.2 a
  obtain ⟨V, hV, f, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf s0
  obtain ⟨t, htV, hgt⟩ := hU.exists_basicOpen_le ⟨genPt ξ, hV⟩ hgU
  have hD : genPt ξ ∈ X.basicOpen t := hgt
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X U hU t
    ((X.presheaf.map (homOfLE htV).op).hom f)
  have hy' : (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom y =
      ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom t) ^ n *
        (X.presheaf.map (homOfLE htV).op).hom f := hy
  have h2 : (X.presheaf.germ U (genPt ξ) hgU).hom y =
      ((X.presheaf.germ U (genPt ξ) hgU).hom t) ^ n * (X.presheaf.germ V (genPt ξ) hV).hom f := by
    have h2' := congrArg (X.presheaf.germ (X.basicOpen t) (genPt ξ) hD).hom hy'
    simp only [map_mul, map_pow, gres] at h2'
    exact h2'
  let ψ : X.presheaf.stalk (genPt ξ) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
  have hφ : ∀ r, φ r = ψ ((X.presheaf.germ U (genPt ξ) hgU).hom r) := by
    intro r
    first
      | rfl
      | simp [φ, ψ]
  have hs0' : ψ ((X.presheaf.germ V (genPt ξ) hV).hom f) = a := hs0
  have h3 : φ y = φ t ^ n * a := by
    rw [hφ, hφ, h2, map_mul, map_pow, hs0']
  have hunit : IsUnit ((X.presheaf.germ U (genPt ξ) hgU).hom t) :=
    (X.mem_basicOpen t (genPt ξ) hgU).mp hD
  have hφt : φ t ≠ 0 := by
    rw [hφ]
    exact (hunit.map ψ).ne_zero
  refine ⟨φ y, key y, φ (t ^ n), key (t ^ n), ?_, ?_⟩
  · rw [map_pow]
    exact pow_ne_zero _ hφt
  · rw [map_pow]
    exact eq_div_of_mul_eq (pow_ne_zero _ hφt) (by rw [h3]; ring)

end GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.PullReg

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {Ω' : Type} [Field Ω']

theorem germ_stalkClosedPointTo_baseChange (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* Ω')
    (ζ : Spec (CommRingCat.of Ω') ⟶ X) (hζ : ζ = Spec.map (CommRingCat.ofHom i) ≫ ξ) (U : X.Opens)
    (hU : ζ (IsLocalRing.closedPoint (CommRingCat.of Ω')) ∈ U) (hU' : genPt ξ ∈ U) :
    X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo ζ =
      X.presheaf.germ U (genPt ξ) hU' ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
  have e : ζ = Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
      X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) := by
    rw [hζ, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hl : IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom := by
    refine ⟨fun a ha => ?_⟩
    have h1 : IsUnit (i ((Scheme.stalkClosedPointTo ξ).hom a)) := ha
    have h2 : IsUnit ((Scheme.stalkClosedPointTo ξ).hom a : Ω) :=
      isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at h1
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo ξ).hom a h2
  subst e
  exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk _ U hU

theorem stalkMap_comp_genMap {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} (hD : Dominates ξ' ξ f i)
    (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1) (s : X.presheaf.stalk (f p'.1)) :
    genMap ξ' p' ((f.stalkMap p'.1).hom s) = i (genMap ξ ⟨f p'.1, h⟩ s) := by
  have key : f.stalkMap p'.1 ≫ X'.presheaf.stalkSpecializes p'.2 ≫ Scheme.stalkClosedPointTo ξ' =
      X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
    have hg : genPt ξ ∈ U := h.mem_open U.2 hU
    have hg' : (ξ' ≫ f) (IsLocalRing.closedPoint (CommRingCat.of Ω')) ∈ U := by
      have : (ξ' ≫ f) (IsLocalRing.closedPoint (CommRingCat.of Ω')) = genPt ξ :=
        (Scheme.Hom.comp_apply ξ' f _).trans hD.map_genPt
      rw [this]; exact hg
    have e := germ_stalkClosedPointTo_baseChange ξ i (ξ' ≫ f) hD U hg' hg
    rw [Scheme.stalkClosedPointTo_comp] at e
    have e3 : f.stalkMap p'.1 ≫ X'.presheaf.stalkSpecializes p'.2 ≫ Scheme.stalkClosedPointTo ξ' =
        X.presheaf.stalkSpecializes (p'.2.map f.continuous) ≫ f.stalkMap (genPt ξ') ≫
          Scheme.stalkClosedPointTo ξ' :=
      (Scheme.Hom.stalkSpecializes_stalkMap_assoc f _ _ p'.2 _).symm
    rw [e3, TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]
    exact e
  exact congrArg (fun φ => φ.hom s) key

end GlobalTheory.CompanionTheory.Ar.Flat.PullReg

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem pull_reg_and_gen : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0})
    (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'),
    Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1,
      (∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧
        ∀ (L : Lat ξ Ω) (t : Ω), L.IsGenAt ⟨f p'.1, h⟩ t →
          (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t) := by
  intro X Ω _ ξ X' Ω' _ ξ' f i hD p'
  have h := hD.specializes p'
  have hreg : ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨_, PullReg.stalkMap_comp_genMap hD p' h s⟩
  refine ⟨h, hreg, fun L t ht => ⟨(map_ne_zero i).2 ht.1, ?_⟩⟩
  rw [Lat.pull_apply L hD]
  have hL : L ⟨f p'.1, hD.specializes p'⟩ = Submodule.span (regAt ξ ⟨f p'.1, h⟩) {t} := ht.2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ Submodule.span (regAt ξ ⟨f p'.1, h⟩) {t} := by
      rw [← hL]; exact he
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 he'
    refine Submodule.mem_span_singleton.2 ⟨⟨i r, hreg _ r.2⟩, ?_⟩
    show i (r : Ω) * i t = i ((r : Ω) * t)
    rw [map_mul]
  · rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.subset_span ⟨t, ?_, rfl⟩
    show t ∈ (L ⟨f p'.1, hD.specializes p'⟩ : Set Ω)
    rw [hL]
    exact Submodule.mem_span_singleton_self t

end GlobalTheory.CompanionTheory.Ar.Flat
end

