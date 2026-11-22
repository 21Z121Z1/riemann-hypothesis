import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecValMulGenVal
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstFamValues

open ConstThetaSections ConstFam

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b}

omit [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem ex_add_nsmul (Λ : GtAn a) (j : ℕ) (α mu : Λ.A.X) :
    Λ.u.ex (Λ.A.ct α + j • Λ.A.ct mu) = a.D₀.c (Λ.ε α + j • Λ.ε mu) := by
  rw [← map_nsmul, ← map_add, ← map_nsmul, ← map_add, Λ.ct]

omit [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem expo_eq (Λ : GtAn a) (j : ℕ) (α mu : Λ.A.X) : expo a j (Λ.ε α) (Λ.ε mu) = Λ.A.exponent j α mu := by
  rw [expo, AnArc.exponent, AnArc.q, Λ.be_eq, Λ.be_eq]

theorem secVal_mul_genVal (Λ : GtAn a) (j : ℕ) (α mu : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (v : Λ.A.V) :
    FrameValue.secVal Λ.u a.D₀.P.isLB (feTranslate a.D₀ j (Λ.ε mu) (Λ.ε α) s₀) (Λ.u.ex v.2).left
        ![v.2, v.2 + (Λ.A.ct α + j • Λ.A.ct mu), Λ.A.ct α + j • Λ.A.ct mu, 0] *
      FrameValue.genVal Λ.u a.D₀.P.isLB ((Λ.ex0 v).s (Λ.ε α + j • Λ.ε mu)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
        ![(Λ.A.ct α + j • Λ.A.ct mu) + v.2, Λ.A.ct α + j • Λ.A.ct mu, v.2, 0] =
      Λ.A.term j α (Λ.fn j α s₀) mu v := by
  have h₁ : ∀ y x z, x = Λ.ε y → z = Λ.A.ct y → FrameValue.genVal Λ.u a.D₀.P.isLB ((Λ.ex0 v).s x)
      (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![z + v.2, z, v.2, 0] = eTwoPi (v.1 y) := by
    rintro y _ _ rfl rfl
    exact Λ.arcDict_expZero_section v y
  have h₂ : ∀ y x z, x = Λ.ε y → z = Λ.A.ct y → FrameValue.genVal Λ.u a.D₀.P.isLB (a.D₀.psi x)
      (Out.jFK (R := ℂ) ℂ) (fun _ => z) = Λ.A.psi y := by
    rintro y _ _ rfl rfl
    exact Λ.psi y
  refine (congrArg₂ (· * ·) (secVal_feTranslate Λ.ah Λ.rig j (Λ.ct α) (Λ.ct mu) (Λ.psi α) (Λ.psi mu)
    (h₂ (mu + α) _ _ (map_add _ _ _).symm (map_add _ _ _).symm) s₀ v.2)
    (h₁ (α + j • mu) _ _ (by rw [map_add, map_nsmul]) (by rw [map_add, map_nsmul]))).trans ?_
  change Λ.fn j α s₀ (v.2 + Λ.A.ct mu) * _ * _ = _
  have n₁ := (Λ.A.psi mu).ne_zero
  have n₂ := (Λ.A.psi α).ne_zero
  simp only [AnArc.term, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Λ.A.psi_add]
  field_simp

end

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e) (j : ℕ) [NeZero j] (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (m : ℕ) (f : ∀ x, ConstFam.SecBMod W.P.D.toPre j x) (σ : Out.H0 W.P.U.LG.L j), ConstFam.IsIntegralForm hW j (Λ.ε α) s₀ m f → (∀ n, W.P.U.toUnifPre.ExpandsAt n j σ f) → Ξ.Vals σ (fun v => HahnSeries.single (m : ℤ) (1 : ℂ) * Λ.A.FSum j α (Λ.fn j α s₀) v) := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ hW j _ α s₀ m f σ hf hE v jL hL
  have hj : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (NeZero.ne j)
  have hm : ∀ mu, 0 ≤ (m : ℤ) + Λ.A.exponent j α mu := fun mu => expo_eq Λ j α mu ▸ (hf.1 (Λ.ε mu)).1
  have hJ : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} :=
    Ideal.map_id _
  have : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ :=
    hJ.symm ▸ (admissibleBase_powerSeries ℂ).2.2.2
  have hb : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
    ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  replace hM := (top_le_iff_cpt (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) _).2 hM
  obtain ⟨j₀, h₀⟩ : ∃ j₀, ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := ⟨_, FrameValue.le_chartAt a.D₀.P.isLB _⟩
  have hd := ConstTerm.le_div (M := W.P.D.toPre.P.L) (φ := W.φ) (k := j₀) (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left)
    (hb ▸ FormalValue.top_le_comp h₀ _) hM
  have hτ := Ξ.τ_eq v jL jM j₀ hL hd
  have hu := FormalValue.isUnit_valR _ _ hd (W.w.s (fun _ => j₀, jM))
  choose jf jt hc using FormalValue.exists_cohCharts (Ξ.g v) jM hM
  have hs := exists_sum_sub_mem (i := fun mu => W.e (Λ.ε α + j • Λ.ε mu))
    (fun _ _ h => Λ.ε.injective (FamFree.add_nsmul_inj hj _ _ _ (W.e.injective h)))
    (n := fun mu => ((m : ℤ) + Λ.A.exponent j α mu).toNat)
    (c := fun mu => Λ.A.term j α (Λ.fn j α s₀) mu v * Λ.u.fr j₀ v.2 ^ j)
    (h := fun x => valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ (W.w.s (fun _ => j₀, jM)).val ^ j *
      (FormalValue.famVal (Ξ.g v) (f x) (jf x) * FormalValue.coordVal (Ξ.g v) x (jt x)))
    (fun mu => by
      rw [(hf.1 (Λ.ε mu)).2, ← secVal_mul_genVal, ← expo_eq]
      exact ConstTerm.core Λ.u (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (PowerSeries.C (R := ℂ)) W.w (Ξ.g v) (Λ.ex0 v)
        (ex_add_nsmul Λ j α mu) (Λ.ex0_b v) (Ξ.g_rel v _) _ _ _
        (fun p => valR_smul_pullB hW j _ _ _ _ p _) jM j₀ _ _ (hc _) hd)
    (fun x hx => by
      have e : f x = 0 := hf.2 x fun mu h => hx (Λ.ε.symm (W.e.symm mu)) (by
        rw [Λ.ε.apply_symm_apply, map_add_nsmul, W.e.apply_symm_apply, h])
      have e' : FormalValue.famVal (Ξ.g v) (f x) (jf x) = 0 := by
        rw [e]
        exact (HolHom.valR_eq _ _ (hc x).1 _).trans (map_zero _)
      rw [e', zero_mul, mul_zero])
    (L := fun k => Λ.A.level j α ((k : ℤ) - m)) (fun k mu => by
      have := hm mu
      rw [AnArc.mem_level]
      omega)
  beta_reduce
  rw [← algebraMap_mk_eq Λ.A j α _ v hm, ← map_pow, ← map_mul]
  refine congrArg _ ((hu.pow j).mul_left_cancel (FormalValue.eq_of_forall_mk_eq
    ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) fun e => Ideal.Quotient.eq.2 ?_))
  obtain ⟨F, -, hF⟩ := ((FormalValue.value_eq_sum_expansion (admissibleBase_powerSeries ℂ) W.P.U (Ξ.g v) (Ξ.x v).left
    (Ξ.x_fm v)).2 j σ f hE).1 e
  obtain ⟨F', hFF, h₂⟩ := hs (e + 1) F
  have h₁ := hF F' jL jM jf jt hFF hL hM fun x _ => hc x
  have e₁ : (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m),
      Λ.A.term j α (Λ.fn j α s₀) mu v * Λ.u.fr j₀ v.2 ^ j) =
      (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α (Λ.fn j α s₀) mu v) *
        PowerSeries.C (Λ.u.fr j₀ v.2) ^ j := by
    ext k
    rw [← map_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, PowerSeries.coeff_mk, Finset.sum_mul]
  rw [e₁, ← Finset.mul_sum, ← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow] at h₂
  replace h₂ := Ideal.pow_right_mono hJ.ge (e + 1) h₂
  have h₃ := congrArg (· ^ j) hτ
  simp only [mul_pow] at h₃
  convert add_mem (Ideal.mul_mem_left _ (valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ (W.w.s (fun _ => j₀, jM)).val ^ j) h₁)
    (Ideal.mul_mem_left _ ((FormalValue.tau W.P.U.toUnifPre ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map
      (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) (Ξ.x v).left jL jM).val ^ j) h₂) using 1
  linear_combination (-(PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m),
    Λ.A.term j α (Λ.fn j α s₀) mu v)) * h₃

end GlobalTheory.ConstFamValues
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SpecialisedPointsHolomorphicQuasiPeriodic
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecHol

open Filter Topology GlobalTheory.Specialise GlobalTheory.HolHom GlobalTheory.CoordFamily

theorem ev_comb_factor : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∀ lin cst, IsFactor A lin cst → ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ (j : ℕ) [NeZero j] (f : A.V → Conv.halfRing T), IsComb A j (Conv.halfRing T) (fun v => f v) → ∀ w hw la v, Conv.ev T w hw (f (v + A.Pw w la)) = Complex.exp (lin w la v + cst w la) ^ j * Conv.ev T w hw (f v) := by
  intro O _ _ A lin cst hF
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  refine ⟨T₀, fun T hT j _ f hf w hw la v => ?_⟩
  obtain ⟨n, r, α, th, h1, h2⟩ := hf
  have key : ∀ z, Conv.ev T w hw (f z) =
      ∑ i, Conv.ev T w hw ⟨r i, (h1 i).1⟩ * A.Sum j (α i) (th i) w z := by
    intro z
    have hm : ∀ i, A.FSum j (α i) (th i) z ∈ Conv.halfRing T :=
      fun i _ hw' => (AnArc.hasSum_coeff_FSum (h₀.mono hT) (h1 i).2 hw' z).summable
    have hv : ∀ i, Conv.ev T w hw ⟨_, hm i⟩ = A.Sum j (α i) (th i) w z :=
      fun i => Conv.ev_eq_of_hasSum hw _ (AnArc.hasSum_coeff_FSum (h₀.mono hT) (h1 i).2 hw z)
    have e : f z = ∑ i, (⟨r i, (h1 i).1⟩ : Conv.halfRing T) * ⟨_, hm i⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      exact h2 z
    rw [e, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hv i]
  rw [key, key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hF.sum w la v j (α i) (th i) (h1 i).2]
  ring

theorem of_coords (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H)
    (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B)
    (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ)
    (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) (hF : IsFactor A lin cst) (N : ℕ) [NeZero N]
    (C : Coords Φ N) :
    ∃ T' ≥ Ψ.T, ∀ w : ℂ, T' < w.im → (∀ z, HolAt (fun v => (Ψ.pi w v).left) z) ∧
      (∀ la v, Ψ.pi w (v + A.Pw w la) = Ψ.pi w v) ∧
      (∀ j z, ⊤ ≤ (Ψ.pi w z).left ⁻¹ᵁ o.t.PP.L.U j → DifferentiableAt ℂ (fun v => Ψ.fr w j v ^ N) z) ∧
      ∀ la v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j →
        Ψ.fr w j v ^ N = (Complex.exp (lin w la v + cst w la) * Ψ.fr w j (v + A.Pw w la)) ^ N := by
  obtain ⟨T₁, hT₁, hC, h₁⟩ := SpecCoord.spec_coords E H D l B bb S s o A y Φ Γ Ψ N C
  obtain ⟨T₂, h₂⟩ := GlobalTheory.ArcPts.exists_formal_convergence _ A
  obtain ⟨T₃, h₃⟩ := ev_comb_factor _ A lin cst hF
  set T := max T₁ (max T₂ T₃) with hT
  have e₁ : T₁ ≤ T := le_max_left _ _
  have e₂ : T₂ ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have e₃ : T₃ ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T, le_trans hT₁ e₁, fun w hw => ?_⟩
  have hw₁ : T₁ < w.im := e₁.trans_lt hw
  have hwC : C.T < w.im := hC.trans_lt hw₁
  have hwΨ : Ψ.T < w.im := lt_of_le_of_lt hT₁ hw₁
  obtain ⟨hy, -, hval⟩ := h₁ w hw₁
  let f : Fin C.n → A.V → Conv.halfRing T := fun i v => Subalgebra.inclusion (Conv.halfRing_mono (hC.trans e₁)) (C.cf i v)
  have hf : ∀ i, IsComb A N (Conv.halfRing T) (fun v => f i v) := fun i => by
    obtain ⟨n, r, α, th, h, h'⟩ := C.comb i
    exact ⟨n, r, α, th, fun a => ⟨Conv.halfRing_mono (hC.trans e₁) (h a).1, (h a).2⟩, h'⟩
  let c : Fin C.n → A.V → ℂ := fun i v => Conv.ev C.T w hwC (C.cf i v)
  have hcf : ∀ i v, c i v = Conv.ev T w hw (f i v) := fun i v => Conv.ev_congr hwC hw rfl
  have hd : ∀ i, Differentiable ℂ (c i) := fun i => by
    rw [show c i = fun v => Conv.ev T w hw (f i v) from funext (hcf i)]
    exact (h₂ T e₂ N).2 (f i) (hf i) w hw
  have hp : ∀ la v i, c i (v + A.Pw w la) = Complex.exp (lin w la v + cst w la) ^ N * c i v := fun la v i => by
    rw [hcf, hcf]
    exact h₃ T e₃ N (f i) (hf i) w hw la v
  have hfr := (SpecGroup.specPts_group E H D l B bb S s o A y Φ Γ Ψ w hwΨ).2.2.1
  have hex : ∀ v, ∃ x : Sp ℂ ⟶ (o.t.G.hom ⁻¹ᵁ C.U).toScheme, x ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Ψ.pi w v).left := fun v => by
    have hxU : ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ (o.t.G.hom ⁻¹ᵁ C.U) := by
      rw [← Scheme.Hom.comp_preimage, Over.w]
      exact hy
    exact ⟨IsOpenImmersion.lift (o.t.G.hom ⁻¹ᵁ C.U).ι (Ψ.pi w v).left (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hxU (x := p) trivial), IsOpenImmersion.lift_fac _ _ _⟩
  choose x hx using hex
  have hv : ∀ i v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j →
      valR (x v) ((Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) =
        c i v * Ψ.fr w j v ^ N := fun i v j hj => hval i v (x v) j (hx v) hj
  have hc : ∀ v, HasCoords (x v) C.b fun i => c i v := fun v => hasCoords_powOver o.t.PP.isLB fun j hj => by
    rw [hx] at hj
    exact ⟨((hfr v).1 j hj).unit ^ N, fun i => by simpa using hv i v j hj⟩
  have hi : (o.t.G.hom ∣_ C.U) ≫ C.U.ι = (o.t.G.hom ⁻¹ᵁ C.U).ι ≫ o.t.G.hom := morphismRestrict_ι _ _
  have hy' : ∀ v, x v ≫ (o.t.G.hom ∣_ C.U) = x 0 ≫ (o.t.G.hom ∣_ C.U) := fun v => by
    rw [← cancel_mono C.U.ι, Category.assoc, Category.assoc, hi, ← Category.assoc, ← Category.assoc, hx, hx,
      Over.w, Over.w]
  have hhol : ∀ z, HolAt x z := fun z => holAt_of_coords C.emb hy' hc fun i => hd i z
  have hhol' : ∀ z, HolAt (fun v => (Ψ.pi w v).left) z := fun z => by
    have := (hhol z).comp (o.t.G.hom ⁻¹ᵁ C.U).ι
    simpa only [hx] using this
  have hper : ∀ la v, x v = x (v + A.Pw w la) := fun la v =>
    eq_of_proportional C.emb ((hy' _).trans (hy' _).symm) (hc v) (hc _) (hp la v)
  have hper' : ∀ la v, Ψ.pi w (v + A.Pw w la) = Ψ.pi w v := fun la v =>
    Over.OverMorphism.ext (by rw [← hx, ← hx, ← hper])
  refine ⟨hhol', hper', fun j z hj => ?_, fun la v j hj => ?_⟩
  · obtain ⟨i, hi0⟩ := C.bpf w hwC z
    have hzj : ⊤ ≤ x z ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j) := by
      intro p _
      rw [← hx] at hj
      exact Set.mem_iInter.2 fun _ => hj (x := p) trivial
    have h1 := (hhol z _ hzj).2 ((C.b i).f (fun _ => j))
    have hne : ∀ᶠ v in 𝓝 z, c i v ≠ 0 := (hd i z).continuousAt.eventually_ne hi0
    refine (h1.fun_mul ((hd i z).fun_inv hi0)).congr_of_eventuallyEq
      (((hhol' z _ hj).1.and hne).mono fun v hv' => ?_)
    simp only [valAt'_eq_valR]
    rw [hv i v j hv'.1, mul_comm, inv_mul_cancel_left₀ hv'.2]
  · obtain ⟨i, hi0⟩ := C.bpf w hwC v
    have h1 := hv i v j hj
    have h2 := hv i (v + A.Pw w la) j (by rw [hper']; exact hj)
    rw [← hper, h1, hp] at h2
    apply mul_left_cancel₀ (show c i v ≠ 0 from hi0)
    rw [h2]
    ring

theorem specPts_holomorphic : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ lin cst, IsFactor A lin cst → ∃ T' ≥ Ψ.T, ∀ w : ℂ, T' < w.im → IsHolTo Set.univ (fun v => (Ψ.pi w v).left) ∧ (∀ la, Ψ.pi w (A.Pw w la) = 1) ∧ (∀ j, DifferentiableOn ℂ (Ψ.fr w j) {v | ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j}) ∧ ∀ la v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j v = Complex.exp (lin w la v + cst w la) * Ψ.fr w j (v + A.Pw w la) := by
  intro hL hL2 E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ hA hΦ lin cst hF
  obtain ⟨C₄⟩ := GlobalTheory.SpanFrame.nonempty_coords hL hL2 E H D l B bb S s o A y Φ hA hΦ 4 le_rfl
  obtain ⟨C₅⟩ := GlobalTheory.SpanFrame.nonempty_coords hL hL2 E H D l B bb S s o A y Φ hA hΦ 5 (by norm_num)
  obtain ⟨T₄, hT₄, h₄⟩ := of_coords E H D l B bb S s o A y Φ Γ Ψ lin cst hF 4 C₄
  obtain ⟨T₅, -, h₅⟩ := of_coords E H D l B bb S s o A y Φ Γ Ψ lin cst hF 5 C₅
  refine ⟨max T₄ T₅, le_max_of_le_left hT₄, fun w hw => ?_⟩
  have hw₄ : T₄ < w.im := (le_max_left _ _).trans_lt hw
  obtain ⟨hhol, hper, hd₄, hq₄⟩ := h₄ w hw₄
  obtain ⟨-, -, hd₅, hq₅⟩ := h₅ w ((le_max_right _ _).trans_lt hw)
  obtain ⟨hadd, -, hfr, -⟩ := SpecGroup.specPts_group E H D l B bb S s o A y Φ Γ Ψ w (lt_of_le_of_lt hT₄ hw₄)
  have hne : ∀ v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j v ≠ 0 := fun v j hj => ((hfr v).1 j hj).ne_zero
  refine ⟨isHolTo_of_holAt isOpen_univ fun z _ => hhol z, fun la => ?_, fun j z hz => ?_, fun la v j hj => ?_⟩
  · have h := hper la 0
    rw [hadd] at h
    exact mul_eq_left.1 h
  · refine DifferentiableAt.differentiableWithinAt ?_
    refine ((hd₅ j z hz).fun_mul ((hd₄ j z hz).fun_inv (pow_ne_zero _ (hne z j hz)))).congr_of_eventuallyEq
      ((hhol z _ hz).1.mono fun v hv => ?_)
    have := hne v j hv
    beta_reduce
    field_simp
  · have h := hq₅ la v j hj
    rw [pow_succ _ 4, pow_succ _ 4, ← hq₄ la v j hj] at h
    exact mul_left_cancel₀ (pow_ne_zero _ (hne v j hj)) h

end GlobalTheory.SpecHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentValueEqJetConstantExpansion
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanExp

theorem approx {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
    {A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G)
    {e j : ℕ} {σ : Out.H0 U.LG.L j} {f : ∀ α : D.toPre.X, D.toPre.SecB j α} (h : U.ExpandsAt e j σ f)
    {K : Type} (q : K ≃ D.toPre.X) : ∃ F : Finset K, ∀ (S : Type) [CommRing S] [IsLocalRing S] (J : Ideal S)
      [IsAdicComplete J S] (s : Sp S ⟶ Sp R) (g : Out.GtPt D.toPre (Over.mk s)) (x : Sp S ⟶ G.left),
      FormalValue.IsFormalPt U J g x → ∀ (jL : U.LG.L.ι) (jM : D.toPre.P.L.ι), ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL →
      ⊤ ≤ FormalValue.basePt g ⁻¹ᵁ D.toPre.P.L.U jM → ∀ (ω τ φ p : S) (B : K → S), IsUnit ω → IsUnit τ →
      ω * τ = (FormalValue.tau U J x jL jM).val * φ →
      (∀ α jf jt, FormalValue.CohCharts g (q α) jM jf jt →
        ω ^ j * (FormalValue.famVal g (f (q α)) jf * FormalValue.coordVal g (q α) jt) = B α * φ ^ j) →
      FormalValue.secVal U σ x jL = p * τ ^ j → p - ∑ α ∈ F, B α ∈ J ^ (e + 1) := by
  obtain ⟨F, hF⟩ := FormalValue.map_secVal_eq U h
  refine ⟨F.map q.symm.toEmbedding, fun S _ _ J _ s g x hx jL jM hL hM ω τ φ p B hω hτ e₁ hB hp => ?_⟩
  haveI := isLocalRing_quotient_pow (ne_top_of_isHausdorff J) e
  choose jf jt hc using FormalValue.exists_cohCharts g jM hM
  have e₂ := Ideal.Quotient.eq.1 ((hF S J s g x hx _ (Ideal.Quotient.mk _) Ideal.mk_ker.ge).2
    ((F.map q.symm.toEmbedding).map q.toEmbedding) jL jM jf jt
    (fun α hα => Finset.mem_map.2 ⟨q.symm α, Finset.mem_map_of_mem _ hα, q.apply_symm_apply α⟩) hL hM
    (fun α _ => hc α))
  rw [Finset.sum_map, hp] at e₂
  have e₃ : ω ^ j * ∑ α ∈ F.map q.symm.toEmbedding, FormalValue.famVal g (f (q α)) (jf (q α)) *
      FormalValue.coordVal g (q α) (jt (q α)) = (∑ α ∈ F.map q.symm.toEmbedding, B α) * φ ^ j := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun α _ => hB α _ _ (hc _)
  rw [← Ideal.unit_mul_mem_iff_mem _ ((hω.mul hτ).pow j)]
  have e₄ := Ideal.mul_mem_left _ (ω ^ j) e₂
  have e₅ : (ω * τ) ^ j = (FormalValue.tau U J x jL jM).val ^ j * φ ^ j := by rw [e₁, mul_pow]
  refine (congrArg (· ∈ J ^ (e + 1)) ?_).mp e₄
  rw [mul_sub, mul_sub, mul_left_comm (ω ^ j) (_ ^ j)]
  refine congrArg₂ (· - ·) (by ring) ((congrArg (_ * ·) e₃).trans ?_)
  rw [e₅]
  ring

section Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}
  (Ξ : ConstPts W Λ)

theorem exists_charts (v : Λ.A.V) : ∃ (jM : W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι),
    ⊤ ≤ (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) ∧
    ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
  have hb : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
    ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex v.2).left
  refine ⟨jM, _, (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ?_, hM⟩, h₀⟩
  exact (congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) hb).mpr (FormalValue.top_le_comp h₀ _ trivial)

theorem isUnit_frame (v : Λ.A.V) (k : W.P.U.LG.L.ι) (h : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U k) :
    IsUnit (Ξ.τ v k) := by
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_charts Ξ v
  refine isUnit_of_mul_isUnit_right ((congrArg IsUnit (Ξ.τ_eq v k jM j₀ h hj)).mpr ?_)
  exact (Units.isUnit _).mul ((Ne.isUnit (Λ.u.fr_ne j₀ v.2 h₀)).map _)

theorem differentiable_term (j : ℕ) (α : Λ.A.X) (s : a.D₀.SecB j (Λ.ε α)) :
    Differentiable ℂ fun u : Λ.A.V => Λ.fn j α s u.2 * eTwoPi (u.1 α) := by
  have h₁ := FrameValue.differentiable_secVal (u := Λ.u) a.D₀.P.isLB s (𝟙 _) (q := id) differentiable_id
    (z := fun z => ![z, z + Λ.A.ct α, Λ.A.ct α, 0]) (fun k => by fin_cases k <;> simp <;> fun_prop)
    (fun w => by rw [id, Category.comp_id]; exact ConstTerm.isLift_famφB Λ.u (Λ.ct α) w)
  simp only [id, Category.comp_id] at h₁
  have h₂ : Differentiable ℂ (fun z : Λ.A.V => z.1 α) := (Λ.A.evalCLM α).differentiable.comp differentiable_fst
  exact (h₁.comp differentiable_snd).fun_mul (h₂.const_mul _).cexp

end Points

theorem exists_eq_mul_pow {S : Type} [CommRing S] (s : S) {t : S} (ht : IsUnit t) (j : ℕ) : ∃ p, s = p * t ^ j := by
  obtain ⟨p, hp⟩ := (ht.pow j).dvd (a := s)
  exact ⟨p, hp.trans (_root_.mul_comm _ _)⟩

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) (v : Sp (DualNumber ℂ⟦X⟧) ⟶ W.t.G.left) (z : Λ.A.V) (jL : W.P.U.LG.L.ι) (jM : W.P.D.toPre.P.L.ι) (ω φ₁ τ : DualNumber ℂ⟦X⟧) (j : ℕ) (σ : Out.H0 W.P.U.LG.L j), FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v → ⊤ ≤ v ⁻¹ᵁ W.P.U.LG.L.U jL → ⊤ ≤ FormalValue.basePt g₁ ⁻¹ᵁ W.P.D.toPre.P.L.U jM → IsUnit ω → IsUnit τ → ω * τ = (FormalValue.tau W.P.U.toUnifPre idealEps v jL jM).val * φ₁ → (∀ (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (f : W.P.D.toPre.SecB j (W.e (Λ.ε α))) (r : ℂ⟦X⟧) jf jt, IsConstMul W j (Λ.ε α) s₀ f r → FormalValue.CohCharts g₁ (W.e (Λ.ε α)) jM jf jt → ω ^ j * (FormalValue.famVal g₁ f jf * FormalValue.coordVal g₁ (W.e (Λ.ε α)) jt) = TrivSqZeroExt.inl r * constEps (jet (fun u : Λ.A.V => Λ.fn j α s₀ u.2 * eTwoPi (u.1 α)) z) * φ₁ ^ j) → HasConstExp W σ → ∃ (x : Λ.A.V → ℂ⟦X⟧) (y : DualNumber ℂ⟦X⟧), IsJet x z y ∧ (∀ u k, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k → FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left k = x u * Ξ.τ u k ^ j) ∧ FormalValue.secVal W.P.U.toUnifPre σ v jL = y * τ ^ j := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ g₁ v z jL jM ω φ₁ τ j σ hv hL hM hω hτ e₁ hB ⟨f, hf, hs⟩
  have hJ : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
  haveI : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
    rw [hJ]; infer_instance
  haveI := isAdicComplete_idealEps
  haveI := isLocalRing_dual ℂ⟦X⟧
  choose s₀ r hs using fun α : Λ.A.X => hs (Λ.ε α)
  choose F hF using fun e => approx W.P.U.toUnifPre (hf e) (Λ.ε.trans W.e).toEquiv
  have key : ∀ e u k p, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k →
      FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left k = p * Ξ.τ u k ^ j →
      p - ∑ α ∈ F e, r α * PowerSeries.C (Λ.fn j α (s₀ α) u.2 * eTwoPi (u.1 α)) ∈
        (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ^ (e + 1) := by
    intro e u k p hk hp
    obtain ⟨iM, i₀, hi, -⟩ := exists_charts Ξ u
    refine hF e _ _ _ (Ξ.g u) _ (Ξ.x_fm u) k iM hk (fun y hy => (hi hy).2) _ _ _ p _
      (FormalValue.isUnit_valR (A := ℂ⟦X⟧) (Ξ.g u).b.left _ hi (W.w.s (fun _ => i₀, iM)))
      (isUnit_frame Ξ u k hk) (Ξ.τ_eq u k iM i₀ hk hi) (fun α jf jt hc => ?_) hp
    refine (ConstTerm.main h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j α (s₀ α) _ (r α) (hs α) u iM i₀ jf jt hc hi).trans ?_
    rw [map_mul, map_pow, _root_.mul_assoc]
  have hk : ∀ u, ∃ k, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k := fun u => by
    obtain ⟨k, hk⟩ := exists_chart W.P.U.LG.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x u).left) (cpt ℂ⟦X⟧))
    exact ⟨k, (top_le_iff_cpt _ _).2 hk⟩
  choose k hk using hk
  choose x hx using fun u => exists_eq_mul_pow (FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left (k u))
    (isUnit_frame Ξ u (k u) (hk u)) j
  obtain ⟨y, hy⟩ := exists_eq_mul_pow (FormalValue.secVal W.P.U.toUnifPre σ v jL) hτ j
  refine ⟨x, y, isJet_of_approx fun e => ⟨_, _, IsJet.sum (F e) fun α _ =>
    (isJet_C (differentiable_term j α (s₀ α) 0) z).const_mul (r α), fun u => ?_, ?_⟩, fun u k' hk' => ?_, hy⟩
  · have := key e u _ _ (hk u) (hx u)
    rwa [hJ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
  · exact hF e _ _ _ g₁ v hv jL jM hL hM ω τ φ₁ y _ hω hτ e₁ (fun α jf jt hc => hB α (s₀ α) _ (r α) jf jt (hs α) hc) hy
  · obtain ⟨p, hp⟩ := exists_eq_mul_pow (FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left k')
      (isUnit_frame Ξ u k' hk') j
    rw [hp]
    refine congrArg (· * _) (FormalValue.eq_of_forall_mk_eq
      ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) fun e => ?_)
    exact (Ideal.Quotient.eq.2 (key e u _ _ hk' hp)).trans (Ideal.Quotient.eq.2 (key e u _ _ (hk u) (hx u))).symm

end GlobalTheory.ConstTanExp
end
end

