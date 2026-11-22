import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Formalism.LocalToGlobal.AlgebraicTheory.Bundle0002
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitOnto

section Generic

variable {A : Type} [CommRing A] {n : ℕ}

def adj (c : A →+* A) (G H X : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A := H * (X.map c)ᵀ * G

variable {c : A →+* A} {G H : Matrix (Fin n) (Fin n) A}

theorem adj_add (X Y : Matrix (Fin n) (Fin n) A) : adj c G H (X + Y) = adj c G H X + adj c G H Y := by
  simp only [adj, Matrix.map_add _ (map_add c), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem adj_smul (a : A) (X : Matrix (Fin n) (Fin n) A) : adj c G H (a • X) = c a • adj c G H X := by
  have : (a • X).map c = c a • X.map c := by
    ext i j
    simp
  simp only [adj, this, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem adj_one (h : G * H = 1) : adj c G H 1 = 1 := by
  rw [adj, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one, mul_eq_one_comm.1 h]

theorem adj_mul (h : G * H = 1) (X Y : Matrix (Fin n) (Fin n) A) :
    adj c G H (X * Y) = adj c G H Y * adj c G H X := by
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc G H, h, Matrix.one_mul]

theorem adj_adj (hc : ∀ a, c (c a) = a) (h : G * H = 1) (hG : (G.map c)ᵀ = G) (X : Matrix (Fin n) (Fin n) A) :
    adj c G H (adj c G H X) = X := by
  have h' : H * G = 1 := mul_eq_one_comm.1 h
  have h1 : (H.map c)ᵀ * G = 1 := by
    conv_lhs => rw [← hG]
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one]
  have h2 : (((X.map c)ᵀ).map c)ᵀ = X := by
    ext i j
    exact hc _
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul, h2, hG, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [← Matrix.mul_assoc, h', Matrix.one_mul]

theorem exists_unitary (hc : ∀ a, c (c a) = a) (h : G * H = 1) (hG : (G.map c)ᵀ = G) {e : A} (he : e * e = e)
    (he' : e * c e = 0) (M M' : Matrix (Fin n) (Fin n) A) (hM : e • (M' * M) = e • (1 : Matrix (Fin n) (Fin n) A)) :
    ∃ g : GL (Fin n) A, (g.1.map c)ᵀ * G * g.1 = G ∧ (e + c e) • (g.1 - 1) = g.1 - 1 ∧ e • g.1 = e • M := by
  have hee : c e * c e = c e := by rw [← map_mul, he]
  have he2 : c e * e = 0 := by rw [mul_comm, he']
  set f := 1 - e - c e with hf
  have hcf : c f = f := by rw [hf, map_sub, map_sub, map_one, hc]; ring
  have h1 : e * f = 0 := by rw [hf]; linear_combination -he - he'
  have h2 : c e * f = 0 := by rw [hf]; linear_combination -hee - he'
  have h3 : f * e = 0 := by rw [mul_comm, h1]
  have h4 : f * c e = 0 := by rw [mul_comm, h2]
  have h5 : f * f = f := by linear_combination f * hf - h3 - h4
  set g := e • M + c e • adj c G H M' + f • (1 : Matrix (Fin n) (Fin n) A) with hg
  have hadj : adj c G H g = e • M' + c e • adj c G H M + f • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [hg, adj_add, adj_add, adj_smul, adj_smul, adj_smul, adj_adj hc h hG, adj_one h, hc, hcf, add_comm (c e • _)]
  have hM' : c e • (adj c G H M * adj c G H M') = c e • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [← adj_mul h, ← adj_smul, hM, adj_smul, adj_one h]
  have hinv : adj c G H g * g = 1 := by
    rw [hadj, hg]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, he', hee, he2,
      h1, h2, h3, h4, h5, zero_smul, add_zero, zero_add, Matrix.mul_one, hM, hM']
    rw [← add_smul, ← add_smul, hf]
    simp
  refine ⟨⟨g, adj c G H g, mul_eq_one_comm.1 hinv, hinv⟩, ?_, ?_, ?_⟩
  · change (g.map c)ᵀ * G * g = G
    have := congrArg (G * ·) hinv
    simpa only [adj, ← Matrix.mul_assoc, h, Matrix.one_mul, Matrix.mul_one] using this
  · change (e + c e) • (g - 1) = g - 1
    have h6 : f • g = f • (1 : Matrix (Fin n) (Fin n) A) := by
      simp only [hg, smul_add, smul_smul, h3, h4, h5, zero_smul, zero_add]
    have h7 : e + c e = 1 - f := by rw [hf]; ring
    rw [h7, sub_smul, one_smul, smul_sub, h6, sub_self, sub_zero]
  · change e • g = e • M
    simp only [hg, smul_add, smul_smul, he, he', h1, zero_smul, add_zero]

end Generic

variable {D : D7}

theorem cA_cA (z : Formalism.L2.Theta.AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    have hx : x = ∑ i, V.frame.repr x i • V.frame i := (V.frame.sum_repr x).symm
    rw [hx, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : V.hT (V.frame i) (V.frame.equivFun.symm v) = ∑ j, V.gram i j * v j := by
      rw [Module.Basis.equivFun_symm_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]; rfl
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, h1, smul_zero]
  exact V.frame.equivFun.symm.injective (this.trans (map_zero _).symm)

theorem gram_mul_inv (V : HSp D) : V.gram.map (incA D) * V.gram⁻¹.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gram_conj (V : HSp D) : ((V.gram.map (incA D)).map (cA D))ᵀ = V.gram.map (incA D) := by
  ext i j
  have h : star (V.gram j i) = V.gram i j := LinearMap.isSymm_def.1 V.herm _ _
  exact congrArg (incA D) h

theorem exists_suppAt_rho_eq : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β x : GL (Fin V.rank) (Fv D.host.F v)), ∃ g : GA D V, SuppAt e V g ∧ rho V π β g = x := by
  intro D e v π he hπ V β x
  obtain ⟨he1, he2, -⟩ := he
  obtain ⟨hs, hk, -, -⟩ := hπ
  have key : ∀ a b, π a = π b ↔ e * a = e * b := fun a b => by
    rw [← sub_eq_zero, ← map_sub, hk, mul_sub, sub_eq_zero]
  have keyM : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (AE D), X.map π = Y.map π ↔ e • X = e • Y := fun X Y => by
    simp only [← Matrix.ext_iff, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, key]
  have lift : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v),
      ∃ X : Matrix (Fin V.rank) (Fin V.rank) (AE D), X.map π = Z := fun Z => by
    choose X hX using fun i j => hs (Z i j)
    exact ⟨Matrix.of X, Matrix.ext hX⟩
  obtain ⟨M, hM⟩ := lift (β * x * β⁻¹).1
  obtain ⟨M', hM'⟩ := lift ((β * x * β⁻¹)⁻¹).1
  obtain ⟨g, h1, h2, h3⟩ := exists_unitary (c := cA D) cA_cA (gram_mul_inv V) (gram_conj V) he1 he2 M M' (by
    rw [← keyM, Matrix.map_mul, hM, hM', Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  let g' : HR (AF D.host.F) D.sp.cm.sig V.gram := ⟨g, h1⟩
  refine ⟨g', fun i j => congrFun (congrFun h2 i) j, Units.ext ?_⟩
  refine (rho_val V π β g').trans ?_
  change (β⁻¹).1 * g.1.map π * β.1 = x.1
  rw [(keyM _ _).2 h3, hM, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

end GlobalTheory.SplitOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStdSplit
section
open NumberField IsDedekindDomain Matrix

noncomputable section

namespace GlobalTheory.ColPeriod

open Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.StdReps

theorem splitNonConj_vG {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (i : Fin 2) :
    GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.SplitNonConj (Pr.vG i) := by
  intro P hP Q hQ h
  have h1 : cO X.E (Pr.piG i) ∈ Q.asIdeal := decoFin_mem_of_mem_divs hQ
  have h2 : cO X.E (Pr.piG i) ∈ P.asIdeal := decoFin_mem_of_mem_divs hP
  rw [h, mem_conjP, cO_cO] at h1
  obtain ⟨a, b, e⟩ := hPr.piG_cop i
  apply one_notMem P
  rw [← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem exists_std_split {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 E))}
    (hST : GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.SplitNonConj ST) {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) :
    ∃ γ : UF E n, ∀ P ∈ ST, localization₂ P.asIdeal (gmap γ.1 N) = stdAt E n P ∧
      localization₂ (conjPrime₂ P).asIdeal (gmap γ.1 N) = stdAt E n (conjPrime₂ P) := by
  obtain ⟨g, hg, hc⟩ := exists_unitary_carries hST hN.1
  let f : Sp E n ≃ₗ[E] Sp E n := Matrix.toLin'OfInv (M := gᴴ) (M' := g) hg (mul_eq_one_comm.1 hg)
  have hf : ∀ x, f x = g *ᵥ x := fun x => rfl
  have hU : f ∈ UF E n := by
    intro x y
    rw [hf, hf, hStd_apply, hStd_apply]
    change star (g *ᵥ x) ⬝ᵥ (g *ᵥ y) = star x ⬝ᵥ y
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hg, one_mulVec]
  have huni : IsUnimodular (hStd E n) (gmap f N) := by
    have e : dual (hStd E n) N = N := hN.2
    change dual (hStd E n) (gmap f N) = gmap f N
    rw [dual_gmap f hU, e]
  refine ⟨⟨f, hU⟩, fun P hP => ?_⟩
  have h : localization₂ P.asIdeal (gmap f N) = stdAt E n P := by
    ext x
    rw [mem_localization_gmap, ← (hc P hP).2, ← hf, LinearEquiv.apply_symm_apply]
  exact ⟨h, le_antisymm (localization_conj_le_of_le stdLat_lattice.fg stdLat_unimodular huni h.ge)
    (localization_conj_le_of_le (gmap_lattice f N hN.1).fg huni stdLat_unimodular h.le)⟩

theorem stdMove : StdMove := by
  intro X Pr hPr i n N hN
  obtain ⟨γ, hγ⟩ := exists_std_split (splitNonConj_vG hPr i) hN
  refine ⟨γ, fun Q hQ => ?_⟩
  have h0 : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have h1 := hPr.piG_norm i
    rw [h, mul_zero] at h1
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast h1.symm)
  rw [← hPr.piG_norm i] at hQ
  rcases Q.isPrime.mem_or_mem hQ with h | h
  · have hm : conjPrime₂ Q ∈ Pr.vG i := (Formalism.L2.Col.mem_divs h0 _).2 (by
      change cO X.E (cO X.E (Pr.piG i)) ∈ Q.asIdeal
      rwa [cO_cO])
    have hcc : conjPrime₂ (conjPrime₂ Q) = Q := by
      ext x
      rw [mem_conjP, mem_conjP, cO_cO]
    have := (hγ _ hm).2
    rwa [hcc] at this
  · exact (hγ _ ((Formalism.L2.Col.mem_divs h0 _).2 h)).1

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankReductionRangeAddCorank
section
open Matrix

namespace GlobalTheory.SplitHecke

theorem finrank_range_reduction (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (p : O) (hp : Irreducible p) (n j : ℕ) (a : GL (Fin n) K)
    (A : Matrix (Fin n) (Fin n) O) (hj : j ≤ n) (h : Hk O p j a) (hA : A.map (algebraMap O K) = a.1) :
    Module.finrank (IsLocalRing.ResidueField O)
      (LinearMap.range (A.map (IsLocalRing.residue O)).mulVecLin) + j = n := by
  classical
  obtain ⟨-, h2, u, hu⟩ := h
  obtain ⟨B, hB⟩ := intM_iff.1 h2
  have inj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hAB : A * B = p • (1 : Matrix (Fin n) (Fin n) O) := by
    apply Matrix.map_injective inj
    change (A * B).map (algebraMap O K) = (p • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O K)
    rw [Matrix.map_mul, hA, hB, Matrix.mul_smul, Units.mul_inv]
    ext i k
    by_cases e : i = k <;> simp [e]
  have hdet : Associated A.det (p ^ j) := by
    have : A.det = p ^ j * u := by
      apply inj
      rw [← hu, ← hA, RingHom.map_det]
      rfl
    rw [this]
    exact (associated_mul_unit_left _ _ u.isUnit)
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := GlobalTheory.SmithBetween.smith_between O p hp n j hj A B hAB hdet
  set r := IsLocalRing.residue O with hr
  have hP' : IsUnit (P.map r).det := by
    have := hP.map r
    rwa [RingHom.map_det] at this
  have hQ' : IsUnit (Q.map r).det := by
    have := hQ.map r
    rwa [RingHom.map_det] at this
  have hp0 : r p = 0 := (IsLocalRing.residue_eq_zero_iff p).2 hp.not_isUnit
  have h3 : A.map r * Q.map r = P.map r *
      Matrix.diagonal (fun i : Fin n => if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_mul, Matrix.diagonal_map (map_zero r)]
    congr 2
    funext i
    split_ifs <;> simp [hp0]
  have h4 := congrArg Matrix.rank h3
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ', Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP',
    Matrix.rank_diagonal] at h4
  have h5 : Fintype.card {i : Fin n // (if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) ≠ 0}
      = n - j := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin n =>
        (if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) ≠ 0)
        = Finset.univ.filter fun i : Fin n => i.1 < n - j := by
      ext i
      by_cases e : i.1 < n - j <;> simp only [Finset.mem_filter, Finset.mem_univ, e, if_true, if_false, true_and, ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false]
    rw [this, Fin.card_filter_val_lt]
    omega
  have h6 : (A.map r).rank = n - j := by
    rw [h4]
    convert h5
  change (A.map r).rank + j = n
  omega

end GlobalTheory.SplitHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeElementComponentMemStandardDoubleCoset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitHecke.HeckeComp

variable {D : D7}

theorem mul_mem_intAE {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem smul_mem_latHat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (L : Set (Fin n → E)) (hL : ∀ u : 𝓞 E, ∀ w ∈ L, (u : E) • w ∈ L) {x : Af F ⊗[F] E} {y : Fin n → Af F ⊗[F] E}
    (hx : x ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)})
    (hy : y ∈ latHat F E L) : x • y ∈ latHat F E L := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, w, hw, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, fun v => ?_, (u : E) • w, hL u w hw, ?_⟩
      · rw [map_mul]; exact mul_mem (ha v) (hb v)
      · funext i
        rw [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
    | neg y _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
  | neg y _ h => rw [neg_smul]; exact neg_mem h

theorem smul_mem_LamHat (V : HSp D) {x : Af D.host.F ⊗[D.host.F] D.host.E}
    {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ LamHat V) :
    x • y ∈ LamHat V := by
  refine smul_mem_latHat _ (fun u w hw => ?_) hx hy
  have h1 : ∑ i, ((u : D.host.E) • w) i • V.frame i = (u : D.host.E) • ∑ i, w i • V.frame i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_assoc]
  change ∑ i, ((u : D.host.E) • w) i • V.frame i ∈ V.L0
  rw [h1]
  have h2 := V.L0.smul_mem u hw
  rw [← algebraMap_smul D.host.E u] at h2
  exact h2

theorem det_unit {A O K : Type} [CommRing A] [CommRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) (π : A →+* K) {n : ℕ} (β : GL (Fin n) K)
    (M : Matrix (Fin n) (Fin n) A) {e u u' w : A} (p : O) (k : ℕ) (he1 : π e = 1) (hp : algebraMap O K p = π w)
    (hu : IsInt O (π u)) (hu' : IsInt O (π u')) (huu : e * u * u' = e) (hdet : e * M.det = e * w ^ k * u) :
    ∃ t : Oˣ, ((β⁻¹).1 * M.map π * β.1).det = algebraMap O K (p ^ k * t) := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hu'
  have hab : a * b = 1 := by
    apply hinj
    have h := congrArg π huu
    rw [map_mul, map_mul, he1, one_mul] at h
    rw [map_mul, ha, hb, h, map_one]
  refine ⟨Units.mkOfMulEqOne a b hab, ?_⟩
  have h := congrArg π hdet
  rw [map_mul, map_mul, map_mul, he1, one_mul, one_mul, map_pow, RingHom.map_det] at h
  rw [det_mul, det_mul, mul_right_comm, ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one,
    one_mul, Units.val_mkOfMulEqOne, map_mul, map_pow, hp, ha]
  exact h

theorem fin_mul_mem {e u : AE D} (he : finPart D e ∈ intAE D) (hu : finPart D u ∈ intAE D) :
    finPart D (e * u) ∈ intAE D := by
  have h : finPart D (e * u) = finPart D e * finPart D u := RingHom.map_mul _ e u
  rw [h]
  exact mul_mem_intAE he hu

theorem intM_of_stable {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (hπ : Function.Surjective π) (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)) (hβ : Frame V e π β)
    (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hM : ∀ y : Fin V.rank → AE D, (fun i => finPart D (e * y i)) ∈ LamHat V →
      (fun i => finPart D (e * (M *ᵥ y) i)) ∈ LamHat V) :
    IntM (Ov D v) ((β⁻¹).1 * M.map π * β.1) := by
  intro i j
  choose y hy using fun k => hπ (β.1 k j)
  have h0 : (fun k => π (y k)) = β.1 *ᵥ Pi.single j 1 := by
    funext k
    rw [hy, mulVec_single_one]
    rfl
  have h1 : (fun i => finPart D (e * y i)) ∈ LamHat V := by
    refine (hβ y).2 fun l => ?_
    rw [h0, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, mulVec_single_one]
    exact intM_one l j
  have h2 := (hβ _).1 (hM y h1) i
  have h3 : (fun k => π ((M *ᵥ y) k)) = M.map π *ᵥ (fun k => π (y k)) := by
    funext k
    exact RingHom.map_mulVec π M y k
  rw [h3, h0, mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at h2
  exact h2

theorem fin_mulVec {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} (e : A)
    (M : Matrix (Fin n) (Fin n) A) (y : Fin n → A) :
    (fun i => φ (e * (M *ᵥ y) i)) = M.map φ *ᵥ (fun i => φ (e * y i)) := by
  funext i
  have h : (fun i => φ (e * y i)) = φ ∘ (e • y) := rfl
  rw [h, ← RingHom.map_mulVec, mulVec_smul]
  rfl

theorem clause_in {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} {e : A} (he : e * e = e)
    (M : Matrix (Fin n) (Fin n) A) (y : Fin n → A) :
    (fun i => φ e * (M.map φ *ᵥ (fun i => φ (e * y i))) i) = fun i => φ (e * (M *ᵥ y) i) := by
  funext i
  rw [← fin_mulVec, ← map_mul, ← mul_assoc, he]

theorem clause_out {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} {e : A} (he : e * e = e) (w : A)
    (M N : Matrix (Fin n) (Fin n) A) (hNM : N * M = 1) (y : Fin n → A) (z : Fin n → B)
    (h : (fun a => φ e * (φ w * φ (e * y a))) = fun a => φ e * (M.map φ *ᵥ z) a) :
    (fun i => φ (e * ((w • N) *ᵥ y) i)) = φ e • z := by
  have h1 : (fun i => φ (e * (w • y) i)) = φ e • (M.map φ *ᵥ z) := by
    funext a
    have h2 : φ e * (φ w * φ (e * y a)) = φ (e * (w • y) a) := by
      rw [← map_mul, ← map_mul, Pi.smul_apply, smul_eq_mul]
      congr 1
      linear_combination (w * y a) * he
    rw [← h2]
    exact congrFun h a
  rw [smul_mulVec, ← mulVec_smul, fin_mulVec, h1, mulVec_smul, mulVec_mulVec, ← Matrix.map_mul, hNM,
    Matrix.map_one _ (map_zero φ) (map_one φ), one_mulVec]

set_option maxHeartbeats 1000000 in

theorem hk_of_isHeckeElt : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ (ϖ : D.host.E) (p : Ov D v) (k : ℕ) (α : GA D V), algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D ϖ) → IsHeckeElt V e ϖ k α → Hk (Ov D v) p k (rho V π β α) := by
  intro D e v π he hc V β hβ ϖ p k α hp hα
  obtain ⟨-, -, hin, hout, u, u', hu, hu', huu, hdet⟩ := hα
  obtain ⟨hs, hker, -, hint⟩ := hc
  have hee : e * e = e := he.1
  have hei : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have he1 : π e = 1 := by
    have h := (hker (1 - e)).2 (by rw [mul_sub, mul_one, hee, sub_self])
    rw [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at h
    exact h.symm
  have hinv : Formalism.L2.Theta.mt V α⁻¹ * Formalism.L2.Theta.mt V α = 1 := by
    change (matHom V α⁻¹).1 * (matHom V α).1 = 1
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [rho_val]
    refine intM_of_stable hs V β hβ _ fun y hy => ?_
    rw [← clause_in (finPart D) hee]
    exact hin _ hy
  · have h1 : algebraMap (Ov D v) (Fv D.host.F v) p • ((rho V π β α)⁻¹).1 =
        (β⁻¹).1 * (incA D ϖ • Formalism.L2.Theta.mt V α⁻¹).map π * β.1 := by
      have h2 : (incA D ϖ • Formalism.L2.Theta.mt V α⁻¹).map π =
          π (incA D ϖ) • (Formalism.L2.Theta.mt V α⁻¹).map π := by
        exact Matrix.ext fun i j => RingHom.map_mul π _ _
      rw [← map_inv, rho_val, h2, hp, Matrix.mul_smul, Matrix.smul_mul]
    rw [h1]
    refine intM_of_stable hs V β hβ _ fun y hy => ?_
    obtain ⟨z, hz, h⟩ := hout _ hy
    rw [clause_out (finPart D) hee (incA D ϖ) _ _ hinv y z h]
    exact smul_mem_LamHat V hei hz
  · rw [rho_val]
    have hinj : Function.Injective (algebraMap (Ov D v) (Fv D.host.F v)) := Subtype.val_injective
    have h1 := (hint u).1 (fin_mul_mem hei hu)
    have h2 := (hint u').1 (fin_mul_mem hei hu')
    exact det_unit hinj π β (Formalism.L2.Theta.mt V α) p k he1 hp h1 h2 huu hdet

end GlobalTheory.SplitHecke.HeckeComp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTensorPowers
section
namespace GlobalTheory

theorem locNormPow_tensorPowers : Formalism.L2.AlgTh.LocNormPow := Formalism.L2.AlgTh.local_norm_power

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalizationIntegralScalarStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormalization_integral_scalar : Formalism.L2.AlgTh.LocNormScale := by
  first | exact @GlobalTheory.locNormScale | exact GlobalTheory.locNormScale | (intros; apply GlobalTheory.locNormScale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizationUnimodularCompanionEqStatement
section
open NumberField Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_unimodularCompanion_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E)), Λ.FG → Λ₁.FG → Formalism.HermitianLatticesTheory.loc (K := E) Q Λ = Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁ → Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ₁) := by
  first | exact @GlobalTheory.loc_compan_eq | exact GlobalTheory.loc_compan_eq | (intros; apply GlobalTheory.loc_compan_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCardMatricesMulEqZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_left_kernel_matrices_eq_pow : ∀ (k : Type) [Field k] [Finite k] (m n j : ℕ) (A : Matrix (Fin n) (Fin n) k), Module.finrank k (LinearMap.range A.mulVecLin) + j = n → Nat.card {w : Matrix (Fin m) (Fin n) k // w * A = 0} = Nat.card k ^ (j * m) := by
  first | exact @GlobalTheory.natCard_matrices_mul_eq_zero | exact GlobalTheory.natCard_matrices_mul_eq_zero | (intros; apply GlobalTheory.natCard_matrices_mul_eq_zero <;> assumption)
end

