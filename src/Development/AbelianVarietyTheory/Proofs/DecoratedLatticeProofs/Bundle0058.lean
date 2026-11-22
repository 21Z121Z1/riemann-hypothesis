import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0056
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChebotarevDegreeOneValuationSubrings
section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem chebOmSt_holds : ReciprocityTheory.ChartRestriction.L1.ChebOmSt := by
  intro E Ω _ _ _ _ _ S hS H hn ho _ σ
  obtain ⟨v, hv, hd, -, B, hB, -, φ, hφ, hφσ⟩ := GlobalTheory.Published.cheb_holds E Ω H ho hn σ hS.toFinset
  refine ⟨B, v, φ, ?_, by simpa using hv, ?_, ?_, ?_⟩
  · intro x
    rw [ValuationSubring.mem_nonunits_iff]
    exact hB x
  · have := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
  · refine ⟨hφ.1, fun x hx => ?_⟩
    rw [ValuationSubring.mem_nonunits_iff]
    exact hφ.2 x ((B.valuation_le_one_iff x).2 hx)
  · have := hn.conj_mem _ hφσ σ⁻¹
    simpa [mul_assoc] using this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionChainLatticeEntriesAgree
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.EntryBases

section Frames
variable {k : Type*} [Field k] {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

def ordExp : n ⊕ Fin c → ℤ := Sum.elim (fun _ => 0) (fun i => (i.val : ℤ) + 1)

theorem typeFrame_bas_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (fun y : n ⊕ Fin c => (ϖ : k) ^ ordExp y) := by
  ext (i | i) (j | j) <;> simp [typeFrame, embA, GlobalTheory.SplitFlip.diagGL, ordExp, diagonal, fromBlocks, Matrix.one_apply]
  split_ifs <;> simp [← zpow_natCast]

theorem typeFrame_bas_inv_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val = diagonal (fun y : n ⊕ Fin c => (ϖ : k) ^ (-ordExp y)) := by
  ext (i | i) (j | j) <;> simp [typeFrame, embA, GlobalTheory.SplitFlip.diagGL, ordExp, diagonal, fromBlocks, Matrix.one_apply]
  split_ifs <;> simp [← zpow_natCast]

theorem typeFrame_coords_apply (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (ord' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (a : ι) (b : ι') :
    (typeFrame ϖ ord).coords (typeFrame ϖ ord') x a b =
      (ϖ : k) ^ (ordExp (ord' b) - ordExp (ord a)) * x (ord a) (ord' b) := by
  simp only [LatFrame.coords, typeFrame_bas_val, typeFrame_bas_inv_val, submatrix_apply, diagonal_mul, mul_diagonal]
  dsimp only [typeFrame]
  rw [sub_eq_add_neg, zpow_add₀ (Units.ne_zero ϖ)]
  ring

end Frames

section Index

theorem fIdx_of_lt {κ c n v : ℕ} (h : v < κ) : LocE.fIdx κ c n v = v := by
  unfold LocE.fIdx; rw [if_pos h]

theorem fIdx_of_mid {κ c n v : ℕ} (h₁ : κ ≤ v) (h₂ : v < κ + c) : LocE.fIdx κ c n v = n + (v - κ) := by
  unfold LocE.fIdx; rw [if_neg (by omega), if_pos h₂]

theorem fIdx_of_ge {κ c n v : ℕ} (h : κ + c ≤ v) : LocE.fIdx κ c n v = v - c := by
  unfold LocE.fIdx; rw [if_neg (by omega), if_neg (by omega)]

theorem scE_of_lt {n v : ℕ} (ex : ℕ → ℕ) (h : v < n) : LocE.scE n ex v = 0 := by
  unfold LocE.scE; rw [if_pos h]

theorem scE_add (n i : ℕ) (ex : ℕ → ℕ) : LocE.scE n ex (n + i) = ex i := by
  unfold LocE.scE; rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem stdOrd_place {κ τ j c l n N : ℕ} (h : j + c = l) (hn : n = κ + j * (τ + 1))
    (e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin N) (he : IsOrd (yPos xPos n) e) (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) :
    (e (stdOrd (Fin κ) (Fin τ) j c h a)).val = LocE.fIdx κ c n (zPos a) ∧
      ordExp (stdOrd (Fin κ) (Fin τ) j c h a) = LocE.scE n (fun i => i + 1) (LocE.fIdx κ c n (zPos a)) := by
  have hn' : n = κ + j * τ + j := by rw [hn]; ring
  rcases a with (i | ⟨i, hi⟩) | p
  · rw [stdOrd_eps, he]
    have hz : zPos (κ := κ) (τ := τ) (j := j) (.inl (.inl i) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = i.val := rfl
    rw [hz, fIdx_of_lt i.isLt, scE_of_lt _ (by omega)]
    exact ⟨rfl, rfl⟩
  · by_cases hic : i < c
    · have hs : stdOrd (Fin κ) (Fin τ) j c h (.inl (.inr ⟨i, hi⟩)) = .inr ⟨i, hic⟩ := standardOrderExtendedBasis_apply_low_block (Fin κ) (Fin τ) j c h ⟨i, hic⟩
      rw [hs, he]
      have hz : zPos (κ := κ) (τ := τ) (j := j) (.inl (.inr ⟨i, hi⟩) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = κ + i := rfl
      rw [hz, fIdx_of_mid (by omega) (by omega), Nat.add_sub_cancel_left, scE_add]
      exact ⟨rfl, by simp [ordExp]⟩
    · obtain ⟨m, rfl⟩ : ∃ m, i = c + m := ⟨i - c, by omega⟩
      have hs : stdOrd (Fin κ) (Fin τ) j c h (.inl (.inr ⟨c + m, hi⟩)) = .inl (.inl (.inr ⟨m, by omega⟩)) :=
        stdOrd_f (Fin κ) (Fin τ) j c h ⟨m, by omega⟩
      rw [hs, he]
      have hz : zPos (κ := κ) (τ := τ) (j := j) (.inl (.inr ⟨c + m, hi⟩) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = κ + (c + m) := rfl
      rw [hz, fIdx_of_ge (by omega), scE_of_lt _ (by omega)]
      exact ⟨by simp [yPos, xPos]; omega, rfl⟩
  · rw [stdOrd_d, he]
    have hp : p.1.val * τ + p.2.val < j * τ := by
      have h1 : p.1.val * τ + p.2.val < (p.1.val + 1) * τ := by rw [add_mul, one_mul]; omega
      exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right τ p.1.isLt)
    have hz : zPos (κ := κ) (τ := τ) (j := j) (.inr p : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = κ + l + p.1.val * τ + p.2.val := rfl
    rw [hz, fIdx_of_ge (by omega), scE_of_lt _ (by omega)]
    exact ⟨by simp [yPos, xPos]; omega, rfl⟩

end Index

section Main
variable {E k : Type} [Field E] [Field k]

theorem atN_val {N : ℕ} (v : Fin N → E) (i : Fin N) : Loc.atN v i.val = v i := by
  unfold Loc.atN; rw [dif_pos i.isLt]

theorem eN_val {N : ℕ} (i : Fin N) : Loc.eN E N i.val = Pi.single i 1 := by
  funext l; unfold Loc.eN; rw [Pi.single_apply]; simp [Fin.ext_iff]

theorem typeFrame_coords_toLoc (ι : E →+* k) (q : ℕ) (ϖ : kˣ) (hϖ : (ϖ : k) = ι (q : E))
    {κ τ l j c j' c' n N n' N' : ℕ} (h : j + c = l) (h' : j' + c' = l) (hn : n = κ + j * (τ + 1)) (hn' : n' = κ + j' * (τ + 1))
    (e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin N) (e' : XIx (Fin κ) (Fin τ) j' ⊕ Fin c' ≃ Fin N')
    (he : IsOrd (yPos xPos n) e) (he' : IsOrd (yPos xPos n') e') (x : (Fin N' → E) →ₗ[E] (Fin N → E))
    (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) (b : Ix (Fin κ ⊕ Fin l) (Fin τ) j') :
    (typeFrame ϖ (stdOrd (Fin κ) (Fin τ) j c h)).coords (typeFrame ϖ (stdOrd (Fin κ) (Fin τ) j' c' h')) (toLoc ι e e' x) a b =
      ι (LocE.entB q κ c' n' c n (fun i => i + 1) (fun i => i + 1) x (zPos a) (zPos b)) := by
  rw [map_natCast] at hϖ
  rw [typeFrame_coords_apply]
  obtain ⟨ha1, ha2⟩ := stdOrd_place h hn e he a
  obtain ⟨hb1, hb2⟩ := stdOrd_place h' hn' e' he' b
  simp only [LocE.entB, toLoc]
  rw [← ha2, ← hb2, ← ha1, ← hb1, eN_val, atN_val, map_mul, map_zpow₀, map_natCast, ← hϖ]
  ring

end Main

theorem entries_agree : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (τ j c : ℕ) (h : j + c = s) (n' c' n c₂ : ℕ), n' = κ + j * (τ + 1) → n = κ + (j + 1) * (τ + 1) → c' = c + 1 → c₂ = c → ∀ (e' : XIx (Fin κ) (Fin τ) j ⊕ Fin (c + 1) ≃ Fin (n' + c')) (e : XIx (Fin κ) (Fin τ) (j + 1) ⊕ Fin c ≃ Fin (n + c₂)), IsOrd (yPos xPos n') e' → IsOrd (yPos xPos n) e → ∀ (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c₂) → E)) (a : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) (j + 1) c (by omega))).coords (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) j (c + 1) (by omega))) (toLoc ι e e' x) a b = ι (LocE.entB q κ c' n' c₂ n (fun i => i + 1) (fun i => i + 1) x (zPos a) (zPos b)) := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT τ j c h n' c' n c₂ hn' hn hc' hc₂ e' e he' he x a b
  subst hc' hc₂
  exact typeFrame_coords_toLoc ι q S.ϖ hT.compl.unif _ _ hn hn' e e' he he' x a b

end GlobalTheory.SymBridge.EntryBases
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAddChar
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.SymTieExists
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem hom_extend {A B C : Type} [AddCommGroup A] [AddCommGroup B] [CommGroup C]
    (hC : ∀ n : ℕ, n ≠ 0 → ∀ c : C, ∃ d : C, d ^ n = c) (i : A →+ B) (hi : Function.Injective i)
    (f : A →+ Additive C) : ∃ g : B →+ Additive C, ∀ a, g (i a) = f a := by
  letI : DivisibleBy (Additive C) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨d, hd⟩ := hC n hn (Additive.toMul u)
    exact ⟨Additive.ofMul d, congrArg Additive.ofMul hd⟩
  letI : DivisibleBy (Additive C) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible (Additive C)).extension_property_addMonoidHom i hi f
  exact ⟨g, fun a => DFunLike.congr_fun hg a⟩

theorem circle_roots (n : ℕ) (hn : n ≠ 0) (c : Circle) : ∃ d : Circle, d ^ n = c := by
  obtain ⟨t, ht⟩ := Circle.exp_surjective c
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  exact ⟨Circle.exp (t / n), by rw [← ht, ← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hn']⟩

theorem units_roots (n : ℕ) (hn : n ≠ 0) (c : ℂˣ) : ∃ d : ℂˣ, d ^ n = c := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (c : ℂ) (Nat.pos_of_ne_zero hn)
  have h0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hz
    exact c.ne_zero hz.symm
  exact ⟨Units.mk0 z h0, Units.ext (by simpa using hz)⟩

section Local
variable {k : Type} [Field k] [ValuativeRel k] {F : Type} [CommRing F]

theorem exists_addChar (ϖ : kˣ) (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (r : 𝒪[k] →+* F) (hr : Function.Surjective r)
    (h0 : ∀ x : 𝒪[k], valuation k (x : k) < 1 → r x = 0) (α : AddChar F Circle) (hα : α ≠ 1) :
    ∃ ψ : AddChar k Circle, HasConductor ψ 1 ∧ ∀ x : 𝒪[k], ψ ((x : k) / ϖ) = α (r x) := by
  let i : 𝒪[k] →+ k := (AddMonoidHom.mulRight ((ϖ : k)⁻¹)).comp (𝒪[k]).subtype.toAddMonoidHom
  have hi : Function.Injective i := fun x y h => Subtype.ext (mul_right_cancel₀ (inv_ne_zero ϖ.ne_zero) h)
  obtain ⟨g, hg⟩ := hom_extend circle_roots i hi (α.toAddMonoidHom.comp r.toAddMonoidHom)
  have hv : ∀ x : 𝒪[k], AddChar.toAddMonoidHomEquiv.symm g ((x : k) / ϖ) = α (r x) := fun x => by
    rw [div_eq_mul_inv]
    exact congrArg Additive.toMul (hg x)
  have hϖ1 : valuation k (ϖ : k) < 1 := (hϖ _).2 le_rfl
  have hp : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  refine ⟨AddChar.toAddMonoidHomEquiv.symm g, fun x => ⟨fun h => ?_, fun h y hy => ?_⟩, hv⟩
  · by_contra hx
    rw [Units.val_one, map_one, not_le] at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hxi : valuation k x⁻¹ < 1 := by
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hx
    have h2 := (hϖ _).1 hxi
    have h3 : valuation k (ϖ : k)⁻¹ ≤ valuation k x := by
      rw [map_inv₀] at h2 ⊢
      exact inv_le_of_inv_le₀ (by simp [zero_lt_iff, hx0]) h2
    refine hα (AddChar.ext _ _ fun t => ?_)
    obtain ⟨z, rfl⟩ := hr t
    rw [← hv z]
    refine h _ (le_trans ?_ h3)
    rw [div_eq_mul_inv, map_mul]
    exact mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 z.2)
  · have hy1 : valuation k y ≤ 1 := by simpa using hy.trans h
    have hlt : valuation k (y * ϖ) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hy1) hϖ1
    have h4 := hv ⟨y * ϖ, (Valuation.mem_integer_iff _ _).2 hlt.le⟩
    rw [h0 _ hlt, AddChar.map_zero_eq_one] at h4
    simpa using h4

theorem exists_tame (r : 𝒪[k] →+* F) (h0 : ∀ x : 𝒪[k], valuation k (x : k) < 1 → r x = 0) (χ : Fˣ →* ℂˣ) :
    ∃ μ : kˣ →* ℂˣ, IsTame μ ∧ ∀ u : (𝒪[k])ˣ, μ (Units.map (𝒪[k]).subtype.toMonoidHom u) = χ (Units.map r.toMonoidHom u) := by
  obtain ⟨g, hg⟩ := hom_extend units_roots (MonoidHom.toAdditive (Units.map (𝒪[k]).subtype.toMonoidHom))
    (Units.map_injective Subtype.val_injective) (MonoidHom.toAdditive (χ.comp (Units.map r.toMonoidHom)))
  have hv : ∀ u : (𝒪[k])ˣ, MonoidHom.toAdditive.symm g (Units.map (𝒪[k]).subtype.toMonoidHom u) =
      χ (Units.map r.toMonoidHom u) := fun u => congrArg Additive.toMul (hg (Additive.ofMul u))
  refine ⟨MonoidHom.toAdditive.symm g, fun x hx => ?_, hv⟩
  have hx1 : valuation k (x : k) = 1 := by
    have := Valuation.map_one_add_of_lt (valuation k) hx
    simpa using this
  let x' : 𝒪[k] := ⟨x, (Valuation.mem_integer_iff _ _).2 hx1.le⟩
  have hu : IsUnit x' := by
    by_contra h
    exact absurd (Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 h) (by simp [x', hx1])
  have e : Units.map (𝒪[k]).subtype.toMonoidHom hu.unit = x := Units.ext rfl
  have e2 : Units.map r.toMonoidHom hu.unit = 1 := by
    refine Units.ext ?_
    have := h0 (x' - 1) hx
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this
  rw [← e, hv, e2, map_one]

end Local

section Res
variable {E k : Type} [Field E] [NumberField E]
  [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem reduction_spec (P : HeightOneSpectrum (𝓞 E)) {a : E} (h : IntAt P a) :
    ∃ r, ∃ s ∉ P.asIdeal, algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * redP P a = Ideal.Quotient.mk P.asIdeal r := by
  obtain ⟨r, s, hs, e⟩ := h
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hs' : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hex : ∃ c r, ∃ s ∉ P.asIdeal, algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨(Ideal.Quotient.mk P.asIdeal s)⁻¹ * Ideal.Quotient.mk P.asIdeal r, r, s, hs, e, mul_inv_cancel_left₀ hs' _⟩
  unfold redP
  rw [dif_pos hex]
  exact hex.choose_spec

theorem exists_residue (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k) (hint : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a)
    (hd : DenseRange ι) :
    ∃ r : 𝒪[k] →+* 𝓞 E ⧸ P.asIdeal, Function.Surjective r ∧ (∀ x : 𝒪[k], r x = 0 ↔ valuation k (x : k) < 1) ∧
      ∀ a (h : ι a ∈ 𝒪[k]), r ⟨ι a, h⟩ = redP P a := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have h1 : (1 : 𝓞 E) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hlt : ∀ y : 𝒪[k], IsLocalRing.residue 𝒪[k] y = 0 ↔ valuation k (y : k) < 1 := fun y => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  let j : 𝓞 E →+* 𝒪[k] := (ι.comp (algebraMap (𝓞 E) E)).codRestrict _ fun r =>
    (hint _).2 ⟨r, 1, h1, by simp⟩
  have hj : ∀ r, (j r : k) = ι (algebraMap (𝓞 E) E r) := fun _ => rfl
  let φ : 𝓞 E →+* 𝓀[k] := (IsLocalRing.residue 𝒪[k]).comp j
  have hker : ∀ r ∈ P.asIdeal, φ r = 0 := by
    intro r hr
    refine (hlt _).2 ?_
    by_contra hlt'
    have hv : valuation k (j r : k) = 1 :=
      le_antisymm ((Valuation.mem_integer_iff _ _).1 (j r).2) (not_lt.1 hlt')
    have hr0 : algebraMap (𝓞 E) E r ≠ 0 := by
      intro h
      rw [hj, h] at hv
      simp at hv
    obtain ⟨t, s, hs, e⟩ := (hint (algebraMap (𝓞 E) E r)⁻¹).1 (by
      rw [Valuation.mem_integer_iff, map_inv₀, map_inv₀, ← hj, hv, inv_one])
    apply hs
    have : s = t * r := by
      apply IsFractionRing.injective (𝓞 E) E
      rw [map_mul, ← e, inv_mul_cancel_right₀ hr0]
    rw [this]
    exact Ideal.mul_mem_left _ _ hr
  let φ' : 𝓞 E ⧸ P.asIdeal →+* 𝓀[k] := Ideal.Quotient.lift _ φ hker
  have hφ' : ∀ r, φ' (Ideal.Quotient.mk _ r) = IsLocalRing.residue 𝒪[k] (j r) := fun _ => rfl
  have hred : ∀ a (h : ι a ∈ 𝒪[k]), φ' (redP P a) = IsLocalRing.residue 𝒪[k] ⟨ι a, h⟩ := by
    intro a h
    obtain ⟨r, s, hs, e, e'⟩ := reduction_spec P ((hint a).1 h)
    have hs' : φ' (Ideal.Quotient.mk P.asIdeal s) ≠ 0 := by
      rwa [map_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]
    apply mul_left_cancel₀ hs'
    rw [← map_mul, e', hφ', hφ', ← map_mul]
    congr 1
    apply Subtype.ext
    change ι (algebraMap (𝓞 E) E r) = ι (algebraMap (𝓞 E) E s) * ι a
    rw [← map_mul, e]
  have hsurj : Function.Surjective φ' := by
    intro t
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective t
    have hn : {y : k | valuation k (y - x) < 1} ∈ nhds (x : k) := by
      rw [IsValuativeTopology.mem_nhds_iff']
      exact ⟨1, by simp⟩
    obtain ⟨a, ha⟩ := hd.mem_nhds hn
    have ha' : valuation k (ι a - x) < 1 := ha
    have hm : ι a ∈ 𝒪[k] := by
      have := add_mem ((Valuation.mem_integer_iff _ _).2 ha'.le) x.2
      simpa using this
    refine ⟨redP P a, ?_⟩
    rw [hred a hm, ← sub_eq_zero, ← map_sub]
    exact (hlt _).2 ha'
  let e := RingEquiv.ofBijective φ' ⟨φ'.injective, hsurj⟩
  refine ⟨e.symm.toRingHom.comp (IsLocalRing.residue 𝒪[k]), e.symm.surjective.comp IsLocalRing.residue_surjective,
    fun x => ?_, fun a h => ?_⟩
  · rw [← hlt]
    exact map_eq_zero_iff _ e.symm.injective
  · change e.symm _ = _
    rw [RingEquiv.symm_apply_eq]
    exact (hred a h).symm

end Res

theorem exists_tie : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ)
    (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (ρ κ : ℕ),
    IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ψ₀ ≠ 1 → ∃ S : SymData k (2 * ρ) κ, Comparison₂ P q ι σ₀ ψ₀ χ S := by
  intro E K k _ _ _ _ _ _ _ _ P q ι ϖ σ₀ ψ₀ χ ρ κ hc hϖ hψ₀
  obtain ⟨r, hr, h0, hred⟩ := exists_residue P ι hc.int hc.dense
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  let α : AddChar (𝓞 E ⧸ P.asIdeal) Circle := AddChar.circleEquivComplex.symm (σ₀.toMonoidHom.compAddChar ψ₀)
  have hαv : ∀ t, (α t : ℂ) = σ₀ (ψ₀ t) := fun t =>
    DFunLike.congr_fun (AddChar.circleEquivComplex.apply_symm_apply (σ₀.toMonoidHom.compAddChar ψ₀)) t
  have hα : α ≠ 1 := by
    intro h
    refine hψ₀ (AddChar.ext _ _ fun t => σ₀.injective ?_)
    rw [← hαv, h]
    simp
  obtain ⟨ψ, hψ, hψv⟩ := exists_addChar ϖ hϖ r hr (fun x => (h0 x).2) α hα
  choose μ hμ hμv using fun i =>
    exists_tame r (fun x => (h0 x).2) ((Units.map σ₀.toMonoidHom).comp (χ (i - 1)))
  obtain ⟨L, hL⟩ := GlobalTheory.SymLevelExists.exists_isSymLevel k ψ hψ ϖ hϖ ρ κ (2 * ρ + 1)
  refine ⟨SymData.mk ψ ϖ ρ L μ hμ hψ hϖ rfl hL, hc, fun a ha => ?_, fun i a u ha hu e => ?_⟩
  · have h := hψv ⟨ι a, (hc.int a).2 ha⟩
    rw [hred] at h
    change (ψ (ι (a / (q : E))) : ℂ) = _
    rw [map_div₀, ← hc.unif, ← hαv, ← h]
  · let x : 𝒪[k] := ⟨ι a, (hc.int a).2 ha⟩
    have hx : IsUnit x := by
      by_contra h
      have h1 := (h0 x).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 h)
      rw [hred] at h1
      haveI := P.isPrime
      exact hu.ne_zero h1
    have e1 : Units.map (𝒪[k]).subtype.toMonoidHom hx.unit = u := Units.ext e.symm
    have e2 : Units.map r.toMonoidHom hx.unit = hu.unit := Units.ext (hred a _)
    change (μ (i + 1) u : ℂ) = _
    rw [← e1, hμv, e2, LocE.unitV, dif_pos hu]
    rfl

end GlobalTheory.SymTieExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsComplIsUnif
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.AdicComplMatch
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

section
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_iff (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, e⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hs
    have h2 := congrArg (P.valuation E) e
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact HeightOneSpectrum.valuation_le_one P r
  · intro h
    obtain ⟨r, s, e⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer P a h
    exact ⟨r, s.1, s.2, by rw [mul_comm]; exact e⟩

theorem valuation_absNorm (h : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    P.valuation E ((Ideal.absNorm P.asIdeal : ℕ) : E) = WithZero.exp (-1 : ℤ) := by
  have hm : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have e : ((Ideal.absNorm P.asIdeal : ℕ) : E) = algebraMap (𝓞 E) E ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) := by simp
  rw [e, HeightOneSpectrum.valuation_of_algebraMap]
  have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem P ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) 1).2 (by simpa using hm)
  have h2 := mt (HeightOneSpectrum.intValuation_le_pow_iff_mem P ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) 2).1 h
  have h0 : P.intValuation ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
  rw [← WithZero.exp_log h0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  push_cast at h1 h2
  omega

end

end GlobalTheory.AdicComplMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FreeN
section
open Formalism.L2.Col

noncomputable section
namespace GlobalTheory.SymBridge

def FreeN (k₀ rS r t p p' : ℕ) : Prop :=
  if p < r then (if p' < r then p ≠ p' ∧ symIdx k₀ rS p < symIdx k₀ rS p' ∧ ¬ (p' = k₀ + rS ∧ p < k₀) else True)
  else (if p' < r then False else (p - r) / t ≤ (p' - r) / t)

end GlobalTheory.SymBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightTwoFormalGroupUnramifiedMultiplierStatement
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heightTwo_formalGroup_unramified_multiplier : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (l : ℕ) (σ : K →+* K), Unr K l σ → ResAlg K → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → σ (σ w) = w → ‖σ w - w‖ = 1 → (∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy f e (l : K))‖ = 1) → ∃ ε : K, ‖ε‖ = 1 ∧ CoefLe 1 (e.subst (C ε * ltLog K l)) := by
  first | exact @GlobalTheory.Honda.heightTwo_unitTwist | exact GlobalTheory.Honda.heightTwo_unitTwist | (intros; apply GlobalTheory.Honda.heightTwo_unitTwist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharacterClosedForm
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.SymBridge

theorem iter_lam_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : (P.iter t μ hμ j).J), ∃ (g₀ : P.J) (D : Fin j → GL t k), (g₀ : GL r k).val = (g : GL (Ix r t j) k).val.submatrix Sum.inl Sum.inl ∧ (∀ i, D i ∈ KO k t ∧ (D i).val = Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val i) ∧ (P.iter t μ hμ j).lam g = P.lam g₀ * ∏ i : Fin j, μ (i.val + 1) (Matrix.GeneralLinearGroup.det (D i)) := by
  intro k _ _ _ _ r t _ _ _ _ P μ hμ j
  induction j with
  | zero =>
    intro g
    refine ⟨⟨(reGL (ixZero r t)).symm (g : GL (Ix r t 0) k), g.2⟩, fun i => i.elim0, rfl, fun i => i.elim0, ?_⟩
    rw [Fin.prod_univ_zero, mul_one]
    rfl
  | succ j ih =>
    intro g
    let h : (P.iter t μ hμ j).stepJ t := ⟨(reGL (ixSucc r t j)).symm g, g.2⟩
    obtain ⟨D, hD, eD⟩ := h.2.2.2.2.2
    have eu := TypeDatum.corner_val _ h
    have e := TypeDatum.step_lam_eq _ (μ (j + 1)) (hμ _) h _ eu D eD
    obtain ⟨g₀, D', e0, hD', el⟩ := ih (TypeDatum.corner _ h)
    refine ⟨g₀, Fin.snoc (α := fun _ => GL t k) D' D, ?_, ?_, ?_⟩
    · rw [e0, eu]; rfl
    · intro i
      induction i using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; exact ⟨hD, by rw [eD]; rfl⟩
      | cast i =>
        simp only [Fin.snoc_castSucc]
        refine ⟨(hD' i).1, ?_⟩
        rw [(hD' i).2, eu]; rfl
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
      rw [← mul_assoc, ← el]
      exact e

end GlobalTheory.SymBridge
end

