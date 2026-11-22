import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.Bundle0001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0312
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0849
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingListCharacterProduct
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare.Shift

variable {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n}

theorem natW_top (lam : DomWeight (n + 1)) (a : Fin (n + 1)) :
    (lam.natW a : ℤ) = lam.w a - lam.w (Fin.last n) := by
  have h1 : lam.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dif_pos (Nat.succ_pos n)]
    rfl
  have h2 := lam.anti (Fin.le_last a)
  unfold DomWeight.natW
  rw [h1]
  omega

theorem lamZ_lamN (lam : DomWeight (n + 1)) (a : Fin (n + 1)) :
    lamZ (lamN lam) a = lam.w a - lam.w (Fin.last n) := by
  unfold lamZ
  split_ifs with h
  · exact natW_top lam a
  · have : a = Fin.last n := Fin.ext (by have := a.2; simp; omega)
    simp [this]

theorem lamN_cast (lam : DomWeight (n + 1)) (i : Fin n) :
    (lamN lam i : ℤ) = lam.w i.castSucc - lam.w (Fin.last n) := natW_top lam _

theorem nuNext_cast (lam : DomWeight (n + 1)) (i : Fin n) :
    (nuNext (lamN lam) i : ℤ) = lam.w i.succ - lam.w (Fin.last n) := by
  rw [← lamZ_lamN]
  unfold nuNext lamZ
  simp only [Fin.val_succ]
  split_ifs <;> rfl

theorem natW_low (hE : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg) (i : Fin n) :
    (sg.natW i : ℤ) = sg.w i - lam.w (Fin.last n) := by
  have hi := i.2
  have h0 : 0 < n := by omega
  have h1 : sg.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dif_pos h0]
    exact hE _ (by simp only; omega)
  have h2 : sg.w ⟨n - 1, by omega⟩ ≤ sg.w i := sg.anti (by rw [Fin.le_def]; simp only; omega)
  rw [hE ⟨n - 1, by omega⟩ (by simp only; omega)] at h2
  unfold DomWeight.natW
  rw [h1]
  omega

theorem d0_eq (hE : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg) :
    Formalism.BranchingDeterminantCap.d0 (lamZ (lamN lam)) (fun i => (sg.natW i : ℤ)) = GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.dZero lam sg := by
  unfold Formalism.BranchingDeterminantCap.d0 GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.dZero
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [lamZ_lamN, natW_low hE]
  ring

theorem rename_initMinor (K : Type) [Field K] {s : ℕ} (I : Fin s → Fin (n + 1)) (hs : s ≤ n) :
    incl K n (initMinor K I hs) = initMinor K I (hs.trans (Nat.le_succ n)) := by
  unfold initMinor incl
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp

end GlobalTheory.BrCompare.Shift

open GlobalTheory.BrCompare.Shift in

theorem GlobalTheory.BrCompare.shifted_branching_list_character : ∀ (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n), GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg → GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg → Formalism.BranchingDeterminantCap.Interlace (lamZ (lamN lam)) (fun i => (sg.natW i : ℤ)) ∧ (∀ u ∈ bmList (lamN lam) sg.natW, u ∈ zList lam sg) ∧ ((zList lam sg).map (bmChi (lamN lam) fun s => ((lamN lam s - sg.natW s : ℕ) : ℤ))).prod = Formalism.L2.Col.Br.cBr rfl lam sg ∧ (∀ s, (Formalism.L2.Col.Br.bBr rfl lam sg s).toNat = lamN lam s - sg.natW s) ∧ ∀ (K : Type) [Field K], Formalism.L2.Col.Br.xiBr K rfl lam sg = incl K n (xiB K (lamN lam) sg.natW) := by
  intro n lam sg hI hE
  have hb : ∀ s, (Formalism.L2.Col.Br.bBr rfl lam sg s).toNat = lamN lam s - sg.natW s := by
    intro s
    have h1 := lamN_cast lam s
    have h2 := natW_low hE s
    have h3 : Formalism.L2.Col.Br.bBr rfl lam sg s = lam.w s.castSucc - sg.w s := rfl
    rw [h3]
    omega
  have ha : ∀ s, (Formalism.L2.Col.Br.aBr rfl lam sg s).toNat = sg.natW s - nuNext (lamN lam) s := by
    intro s
    have h1 := nuNext_cast lam s
    have h2 := natW_low hE s
    have h3 : Formalism.L2.Col.Br.aBr rfl lam sg s = sg.w s - lam.w s.succ := rfl
    rw [h3]
    omega
  refine ⟨?_, ?_, ?_, hb, ?_⟩
  · intro i
    have := hI i
    simp only [lamZ_lamN, natW_low hE]
    omega
  · intro u hu
    simp only [bmList, List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_erase, rset, d0_eq hE,
      Finset.mem_Icc] at hu
    simp only [lamZ_lamN, natW_low hE] at hu
    obtain ⟨i, -, v, ⟨h1, h2, h3⟩, rfl⟩ := hu
    simp only [zList, List.mem_flatten, List.mem_ofFn]
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_erase, GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.rangeSet, Finset.mem_Icc]
    exact ⟨v + lam.w (Fin.last n), ⟨by omega, by omega, by omega⟩, by ring⟩
  · unfold zList Formalism.L2.Col.Br.cBr
    rw [List.map_flatten, List.prod_flatten, List.map_map, List.map_ofFn, List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp_def, List.map_map, Finset.prod_map_toList]
    refine Finset.prod_congr rfl fun v _ => ?_
    unfold bmChi
    refine Finset.prod_congr rfl fun j _ => ?_
    have h1 := lamN_cast lam j
    have h2 := natW_low hE j
    have h3 := hI j
    simp only
    omega
  · intro K _
    unfold Formalism.L2.Col.Br.xiBr xiB
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_pow, rename_initMinor, rename_initMinor, ha, hb]
    congr 2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSixth
section
noncomputable section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace EntryDatum

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}

theorem phiT_add {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG') (hd' : d'.Ok)
    (c : 𝓞 E) (hc : ∀ P ∈ ST, c ∈ P.asIdeal) (x z : HomE E a b)
    (hz : ∀ P ∈ ST, ∀ y ∈ d.at P, z y ∈ d'.at P) : phiT K d d' (x + c • z) = phiT K d d' x := by
  have key : ∀ (x z : HomE E a b), (∀ P ∈ ST, ∀ y ∈ d.at P, z y ∈ d'.at P) →
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) →
      ∀ P : ST, ∀ y ∈ d.at P.1, (x + c • z) y ∈ d'.at P.1 ∧ d'.f P ((x + c • z) y) = d.f P y := by
    intro x z hz h P y hy
    obtain ⟨h1, h2⟩ := h P y hy
    have h3 := hz P.1 P.2 y hy
    have h4 : c • z y ∈ d'.at P.1 := Submodule.smul_mem _ c h3
    have e : (x + c • z) y = x y + c • z y := rfl
    rw [e]
    refine ⟨add_mem h1 h4, ?_⟩
    rw [hd'.f_add P _ h1 _ h4, hd'.f_smul P c _ h3, Ideal.Quotient.eq_zero_iff_mem.2 (hc P.1 P.2), zero_mul, add_zero, h2]
  have hiff : (∀ P : ST, ∀ y ∈ d.at P.1, (x + c • z) y ∈ d'.at P.1 ∧ d'.f P ((x + c • z) y) = d.f P y) ↔
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) := by
    refine ⟨fun h => ?_, key x z hz⟩
    have h' := key (x + c • z) (-z) (fun P hP y hy => neg_mem (hz P hP y hy)) h
    have e : x + c • z + c • (-z) = x := by rw [smul_neg, add_neg_cancel_right]
    rwa [e] at h'
  unfold phiT
  by_cases h : ∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y
  · rw [if_pos h, if_pos (hiff.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

theorem phiT_support {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (x : HomE E a b) (hx : phiT K d d' x ≠ 0) : ∀ P ∈ ST, ∀ y ∈ d.at P, x y ∈ d'.at P := by
  intro P hP y hy
  unfold phiT at hx
  split_ifs at hx with h
  · exact (h ⟨P, hP⟩ y hy).1
  · exact absurd rfl hx

theorem norm_phiT_le {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (σ : K →+* ℂ) (x : HomE E a b) : ‖σ (phiT K d d' x)‖ ≤ 1 := by
  unfold phiT
  split_ifs <;> simp

theorem inFr_maps_iff (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    {M M₀ : Submodule (𝓞 E) (Sp E a)} {M' M₀' : Submodule (𝓞 E) (Sp E b)}
    (hf : ∀ x, f x ∈ M ↔ x ∈ M₀) (hf' : ∀ x, f' x ∈ M' ↔ x ∈ M₀') (x : HomE E a b) :
    (∀ y ∈ M₀, inFr f f' x y ∈ M₀') ↔ ∀ y ∈ M, x y ∈ M' := by
  have e : ∀ y, f' (inFr f f' x y) = x (f y) := fun y => by simp [inFr]
  constructor
  · intro h y hy
    have h1 : f.symm y ∈ M₀ := (hf _).1 (by simpa using hy)
    have h2 := (hf' _).2 (h _ h1)
    rw [e] at h2
    simpa using h2
  · intro h y hy
    rw [← hf', e]
    exact h _ ((hf y).2 hy)

theorem inFr_add_smul (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x z : HomE E a b) (q k : ℕ) :
    inFr f f' (x + ((q * k : ℕ) : 𝓞 E) • z) = inFr f f' x + (q : E) • inFr f f' ((k : 𝓞 E) • z) := by
  have e : ∀ n : ℕ, ((n : ℕ) : 𝓞 E) • z = (n : E) • z := fun n => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [e, e]
  refine LinearMap.ext fun y => ?_
  simp [inFr, mul_smul]

theorem smallDatum_prod {ST SG SG' SB S : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (hd' : d'.Ok) (fr : Frs E a SB) (fr' : Frs E b SB)
    (hfr : ∀ (P : SB) x, fr P x ∈ d.at P.1 ↔ x ∈ stdAt E a P.1) (hfr' : ∀ (P : SB) x, fr' P x ∈ d'.at P.1 ↔ x ∈ stdAt E b P.1)
    (hS : ∀ P, P ∈ S ↔ P ∈ ST ∨ P ∈ SB) (c : ℕ) (hc : ∀ P ∈ ST, (c : 𝓞 E) ∈ P.asIdeal) (q : SB → ℕ) (hq : ∀ P, q P ∣ c)
    (Φ : SB → HomE E a b → K) (β : SB → ℝ) (hΦ : ∀ P : SB, LocSmall (q P) (stdAt E a P.1) (stdAt E b P.1) (Φ P) (β P)) :
    SmallDatum S d.N d'.N c (fun x => phiT K d d' x * ∏ P : SB, Φ P (inFr (fr P) (fr' P) x)) (∏ P : SB, β P) := by
  refine ⟨fun x hx P hP => ?_, fun x y hy => ?_, fun σ x => ?_⟩
  · rcases (hS P).1 hP with h | h
    · exact phiT_support d d' x (left_ne_zero_of_mul hx) P h
    · have h1 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) ⟨P, h⟩ (Finset.mem_univ _)
      exact (inFr_maps_iff _ _ (hfr ⟨P, h⟩) (hfr' ⟨P, h⟩) x).1 ((hΦ ⟨P, h⟩).1 _ h1)
  · obtain ⟨z, hz, rfl⟩ := hy
    have e : ((c : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z = (c : 𝓞 E) • z := rfl
    rw [e]
    show phiT K d d' _ * _ = phiT K d d' _ * _
    rw [phiT_add d d' hd' _ hc x z (fun P hP => hz P ((hS P).2 (Or.inl hP)))]
    congr 1
    refine Finset.prod_congr rfl fun P _ => ?_
    obtain ⟨k, hk⟩ := hq P
    rw [hk, inFr_add_smul]
    refine (hΦ P).2.1 _ _ ?_
    refine (inFr_maps_iff _ _ (hfr P) (hfr' P) _).2 fun y hy => ?_
    exact Submodule.smul_mem _ (k : 𝓞 E) (hz P.1 ((hS P.1).2 (Or.inr P.2)) y hy)
  · show ‖σ (phiT K d d' x * _)‖ ≤ _
    rw [map_mul, norm_mul, map_prod, norm_prod]
    have h1 : ∏ P : SB, ‖σ (Φ P (inFr (fr P) (fr' P) x))‖ ≤ ∏ P : SB, β P :=
      Finset.prod_le_prod (fun P _ => norm_nonneg _) fun P _ => (hΦ P).2.2 σ _
    have h0 : 0 ≤ ∏ P : SB, ‖σ (Φ P (inFr (fr P) (fr' P) x))‖ := Finset.prod_nonneg fun P _ => norm_nonneg _
    exact (mul_le_of_le_one_left h0 (norm_phiT_le d d' σ x)).trans h1

end EntryDatum

end GlobalTheory.ColNorms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTensorRetractOfCmDatumRankOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem smul_comm_of_finrank_one (D : Datum H) (h : Module.finrank (𝓞 E) D.La = 1)
    (l : D.La →ₗ[𝓞 E] 𝓞 E) (x y : D.La) : l x • y = l y • x := by
  have := D.fin
  have := D.proj
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨r, s, hr, e⟩ := CMLat.exists_smul_eq_smul h hx y
  have hl : r * l y = s * l x := by rw [← smul_eq_mul, ← map_smul, e, map_smul, smul_eq_mul]
  have h0 : r • (l x • y - l y • x) = 0 := by
    rw [smul_sub, smul_comm r (l x) y, e, smul_smul, smul_smul, hl, mul_comm, sub_self]
  rw [smul_eq_zero] at h0
  exact sub_eq_zero.1 (h0.resolve_left hr)

theorem exists_dualBasis (D : Datum H) :
    ∃ (n : ℕ) (a : Fin n → D.La) (l : Fin n → (D.La →ₗ[𝓞 E] 𝓞 E)), ∀ x, ∑ k, l k x • a k = x := by
  have := D.fin
  have := D.proj
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) D.La
  refine ⟨n, fun k => f (fun j => if k = j then 1 else 0), fun k => LinearMap.proj k ∘ₗ g, fun x => ?_⟩
  have hx : f (g x) = x := LinearMap.congr_fun hfg x
  conv_rhs => rw [← hx, LinearMap.pi_apply_eq_sum_univ f (g x)]
  rfl

theorem exists_sum_comp_eq_id (DA DB : Datum H) (hA : DA.p + DA.q = 1) :
    ∃ (n : ℕ) (α : Fin n → (DA.La →ₗ[𝓞 E] DB.La)) (β : Fin n → (DB.La →ₗ[𝓞 E] DA.La)),
      ∑ i, α i ∘ₗ β i = LinearMap.id := by
  have := DA.fin
  have := DA.proj
  have hr : Module.finrank (𝓞 E) DA.La = 1 := by rw [DA.rank, hA]
  obtain ⟨n, a, l, decA⟩ := exists_dualBasis DA
  obtain ⟨m, b, mu, decB⟩ := exists_dualBasis DB
  have tr : ∑ k, l k (a k) = 1 := by
    have : Nontrivial DA.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hr]; exact one_pos)
    obtain ⟨x, hx⟩ := exists_ne (0 : DA.La)
    have e : (∑ k, l k (a k)) • x = (1 : 𝓞 E) • x := by
      rw [Finset.sum_smul, one_smul]
      conv_rhs => rw [← decA x]
      exact Finset.sum_congr rfl fun k _ => smul_comm_of_finrank_one DA hr (l k) (a k) x
    have h0 : ((∑ k, l k (a k)) - 1) • x = 0 := by rw [sub_smul, e, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hx)
  refine ⟨n * m, fun i => (l (finProdFinEquiv.symm i).1).smulRight (b (finProdFinEquiv.symm i).2),
    fun i => (mu (finProdFinEquiv.symm i).2).smulRight (a (finProdFinEquiv.symm i).1), ?_⟩
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.sum_apply, LinearMap.id_apply]
  rw [finProdFinEquiv.symm.sum_comp (fun p : Fin n × Fin m =>
    ((l p.1).smulRight (b p.2) ∘ₗ (mu p.2).smulRight (a p.1)) y), Fintype.sum_prod_type, Finset.sum_comm]
  conv_rhs => rw [← decB y]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, map_smul, smul_eq_mul, smul_smul]
  rw [← Finset.sum_smul, ← Finset.mul_sum, tr, _root_.mul_one]

end GlobalTheory.CM
end

noncomputable section
namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] {ω : R}
  {C : Ell H R ω}

theorem IsTen.isLinearHom_mapLeft {A B : PAT H (Sp R)} {DA DB : Datum H} {hA : DA.La → DA.La → OK H}
    {hB : DB.La → DB.La → OK H} (tA : IsTen C DA hA A) (tB : IsTen C DB hB B) (φ : DA.La →ₗ[𝓞 E] DB.La) :
    Serre.IsLinearHom A.t.act B.t.act (tA.ten.mapLeft tB.ten (φ.restrictScalars (OK H))) := by
  refine ⟨inferInstance, fun s => ?_⟩
  have := A.t.act.hom s
  have := B.t.act.hom s
  refine tA.ten.hom_ext fun m => ?_
  rw [← Category.assoc, ← tA.lin, Serre.IsTensor.tmul_mapLeft, ← Category.assoc, Serre.IsTensor.tmul_mapLeft,
    LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, map_smul, tB.lin]

theorem IsTen.prod_mapLeft {B : PAT H (Sp R)} {DB : Datum H} {hB : DB.La → DB.La → OK H}
    (tB : IsTen C DB hB B) {I : Type} (s : Finset I) (φ : I → (DB.La →ₗ[𝓞 E] DB.La)) :
    ∏ i ∈ s, tB.ten.mapLeft tB.ten ((φ i).restrictScalars (OK H)) =
      tB.ten.mapLeft tB.ten ((∑ i ∈ s, φ i).restrictScalars (OK H)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, LinearMap.restrictScalars_zero, Serre.IsTensor.mapLeft_zero]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, LinearMap.restrictScalars_add, Serre.IsTensor.mapLeft_add]

theorem isTen_retract_of_rank_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (A B : PAT H (Sp R)) (DA DB : Datum H)
    (hA : DA.La → DA.La → OK H) (hB : DB.La → DB.La → OK H), DA.p + DA.q = 1 → IsTen C DA hA A → IsTen C DB hB B →
    ∃ (n : ℕ) (f : Fin n → (A.t.G ⟶ B.t.G)) (g : Fin n → (B.t.G ⟶ A.t.G)),
      (∀ i, Serre.IsLinearHom A.t.act B.t.act (f i)) ∧ (∀ i, Serre.IsLinearHom B.t.act A.t.act (g i)) ∧
      ∏ i, (g i ≫ f i) = 𝟙 B.t.G := by
  intro E _ _ _ H R _ ω C A B DA DB hA hB h tA tB
  obtain ⟨n, α, β, hαβ⟩ := exists_sum_comp_eq_id DA DB h
  refine ⟨n, fun i => tA.ten.mapLeft tB.ten ((α i).restrictScalars (OK H)),
    fun i => tB.ten.mapLeft tA.ten ((β i).restrictScalars (OK H)),
    fun i => tA.isLinearHom_mapLeft tB (α i), fun i => tB.isLinearHom_mapLeft tA (β i), ?_⟩
  have e : ∀ i, tB.ten.mapLeft tA.ten ((β i).restrictScalars (OK H)) ≫ tA.ten.mapLeft tB.ten ((α i).restrictScalars (OK H))
      = tB.ten.mapLeft tB.ten ((α i ∘ₗ β i).restrictScalars (OK H)) := fun i =>
    (Serre.IsTensor.mapLeft_comp _ _ _ _ _).symm
  simp only [e]
  rw [tB.prod_mapLeft, hαβ]
  exact Serre.IsTensor.mapLeft_id _

end GlobalTheory.CM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGramPosSemidefAndNormAtPlace
section
namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem pairVr_one_eq {E K : Type} [Field E] [Field K] [StarRing K] {ι : Type} [Fintype ι] (emb : ι → E →+* K) {n : ℕ}
    (lam : ι → DomWeight n) :
    pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) = pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) := by
  have e : gramKd emb (1 : Matrix (Fin n) (Fin n) E) = fun _ => 1 := by
    funext τ
    rw [gramKd, Matrix.map_one _ (map_zero _) (map_one _), inv_one, Matrix.transpose_one]
  rw [← e]
  rfl

theorem gram_posSemidef_and_sqAt : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (emb : ι → E →+* K) (n : ℕ) (lam : ι → DomWeight n) (σ : K →+* ℂ), ((Matrix.of fun i j => pairVr emb lam 1 (bVV K lam i) (bVV K lam j)).map σ).PosSemidef ∧ ∀ x : Formalism.L2.DIV.VV K lam, (∑ i, ∑ j, starRingEnd ℂ ((InfinitePlace.mk σ).embedding ((bVV K lam).repr x i)) * (InfinitePlace.mk σ).embedding (pairVr emb lam 1 (bVV K lam i) (bVV K lam j)) * (InfinitePlace.mk σ).embedding ((bVV K lam).repr x j)).re = sqAt σ lam x := by
  intro E K _ _ _ _ _ ι _ emb n lam σ
  rw [pairVr_one_eq]
  refine ⟨?_, fun x => ?_⟩
  · simp only [GlobalTheory.PeriodClassSum.pairK_one_basis]
    exact (GlobalTheory.PeriodClassSum.gramB_posDef lam σ).posSemidef
  · unfold sqAt
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h, ← Complex.conj_re]
      simp only [map_sum, map_mul, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

end GlobalTheory.ColNorms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaHalfMulUnrTorus
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp ValuativeRel NumberField IsDedekindDomain
open scoped NNReal

noncomputable section
namespace GlobalTheory.LGrp.BorelCompletion

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem ordV_eq (x : v.adicCompletion F) : Formalism.UG.ordV F v x = -WithZero.log (Valued.v x) := by
  unfold Formalism.UG.ordV
  split_ifs with h
  · simp [h]
  · rw [WithZero.toAdd_unzero_eq_log]

theorem nabs_completion (x : (v.adicCompletion F)ˣ) :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    GlobalTheory.SplitWeil.nabs (v.adicCompletion F) x =
      (Formalism.UG.qV F v : ℝ) ^ (WithZero.log (Valued.v (x : v.adicCompletion F))) := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  have hO : 𝒪[v.adicCompletion F] = (v.adicCompletionIntegers F).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  have hq : GlobalTheory.SplitWeil.resCard (v.adicCompletion F) = Formalism.UG.qV F v := by
    rw [← Formalism.UG.P.tjcosets_card_residue]
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr hO)).toEquiv
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hπ.symm.trans (map_zero _))
  have hle : ∀ y : 𝒪[v.adicCompletion F], Valued.v (y : v.adicCompletion F) ≤ 1 := fun y =>
    he.le_one_iff_le_one.1 ((Valuation.mem_integer_iff _ _).1 y.2)
  have hunit : ∀ y : 𝒪[v.adicCompletion F], IsUnit y ↔ Valued.v (y : v.adicCompletion F) = 1 := fun y => by
    rw [← he.eq_one_iff_eq_one]
    exact (Valuation.integer.integers (valuation (v.adicCompletion F))).isUnit_iff_valuation_eq_one
  have hπO : π ∈ 𝒪[v.adicCompletion F] := by
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hirr : Irreducible (⟨π, hπO⟩ : 𝒪[v.adicCompletion F]) := by
    refine ⟨?_, fun a b hab => ?_⟩
    · rw [hunit]
      show Valued.v π ≠ 1
      rw [hπ, ← WithZero.exp_zero, Ne, WithZero.exp_inj]
      norm_num
    · have h1 : Valued.v (a : v.adicCompletion F) * Valued.v (b : v.adicCompletion F) =
          WithZero.exp (-1 : ℤ) := by
        rw [← hπ, ← map_mul]
        exact congrArg _ (congrArg Subtype.val hab).symm
      have ha : Valued.v (a : v.adicCompletion F) ≠ 0 := left_ne_zero_of_mul (by rw [h1]; simp)
      have hb : Valued.v (b : v.adicCompletion F) ≠ 0 := right_ne_zero_of_mul (by rw [h1]; simp)
      have ha1 := hle a
      have hb1 := hle b
      rw [hunit, hunit]
      rw [← WithZero.exp_log ha] at h1 ha1 ⊢
      rw [← WithZero.exp_log hb] at h1 hb1 ⊢
      rw [← WithZero.exp_add, WithZero.exp_inj] at h1
      rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
      rw [← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
      omega
  have h1 := GlobalTheory.SplitWeil.nabs_uniformiser hirr (x := Units.mk0 π hπ0) rfl
  rw [hq] at h1
  set m := WithZero.log (Valued.v (x : v.adicCompletion F)) with hm
  have hx : Valued.v (x : v.adicCompletion F) = WithZero.exp m := (WithZero.exp_log (by simp)).symm
  have h2 : GlobalTheory.SplitWeil.nabs (v.adicCompletion F) (x * (Units.mk0 π hπ0) ^ m) = 1 := by
    apply GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one
    rw [he.eq_one_iff_eq_one, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0,
      hπ, hx, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have h3 : GlobalTheory.SplitWeil.nabs (v.adicCompletion F) ((Units.mk0 π hπ0) ^ m) = ((Formalism.UG.qV F v : ℝ)⁻¹) ^ m := by
    rw [← h1]
    simp only [GlobalTheory.SplitWeil.nabs, map_zpow, NNReal.coe_zpow]
  rw [GlobalTheory.SplitWeil.nabs_mul, h3, inv_zpow] at h2
  exact (eq_inv_of_mul_eq_one_left h2).trans (inv_inv _)

theorem sqrt_zpow_eq (q : ℕ) (m e : ℤ) :
    ((Real.sqrt (((q : ℝ) ^ m) ^ e) : ℝ) : ℂ) = (q : ℂ) ^ ((m : ℂ) * ((e : ℂ) / 2)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [Real.sqrt_eq_rpow, ← zpow_mul, ← Real.rpow_intCast, ← Real.rpow_mul hq, Complex.ofReal_cpow hq]
  congr 1
  push_cast
  ring

theorem deltaHalf_mul_unrTorus : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) [LocallyCompactSpace (v.adicCompletion F)] (n : ℕ) (α : Fin n → ℂˣ) (b : (borelGL (v.adicCompletion F) (Fin n)).Q), (((borelGL (v.adicCompletion F) (Fin n)).deltaHalf b : ℂˣ) : ℂ) * ((unrTorus (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom α ((borelGL (v.adicCompletion F) (Fin n)).p b) : ℂˣ) : ℂ) = Formalism.UG.chiDelta F v (fun i => (α i : ℂ)) b.1 := by
  intro F _ _ v _ n α b
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  have h := GlobalTheory.BorelModulus.delta_borelGL (v.adicCompletion F) n b
  rw [LeviDatum.deltaHalf_coe, h, Real.sqrt_prod _ (fun i _ => zpow_nonneg (GlobalTheory.SplitWeil.nabs_pos _ _).le _),
    unrTorus_apply, Formalism.UG.chiDelta, Complex.ofReal_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : (((borelGL (v.adicCompletion F) (Fin n)).p b i : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (b.1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i := rfl
  rw [nabs_completion, sqrt_zpow_eq, unrChar_apply, ordV_eq, e, mul_comm, Units.val_zpow_eq_zpow_val]
  congr 2
  push_cast
  ring

end GlobalTheory.LGrp.BorelCompletion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealRoundingRealExponentsBadPrimesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_rounding_realExponents_badPrimes : ∀ (K : Type) [Field K] [NumberField K] (B : Finset ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ), (∀ p ∈ B, p.Prime) → (Function.support ρ).Finite → (∀ w : HeightOneSpectrum (𝓞 K), (∀ p ∈ B, ((p : ℕ) : 𝓞 K) ∉ w.asIdeal) → ∃ n : ℤ, ρ w = n) → ∃ (a : K) (𝔞 : Ideal (𝓞 K)), a ≠ 0 ∧ 𝔞 ≠ ⊥ ∧ (∀ b ∈ 𝔞, b ≠ 0 → ∀ w, 0 ≤ (vAdd w ((b : K) * a) : ℝ) + ρ w) ∧ (∑ᶠ w, ρ w * lw K w) - ∑ p ∈ B, Real.log p ≤ -((∑ σ : K →+* ℂ, Real.log ‖σ a‖) / (Module.finrank ℚ K : ℝ)) - Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) := by
  first | exact @GlobalTheory.Rounding.exists_rounding | exact GlobalTheory.Rounding.exists_rounding | (intros; apply GlobalTheory.Rounding.exists_rounding <;> assumption)
end

