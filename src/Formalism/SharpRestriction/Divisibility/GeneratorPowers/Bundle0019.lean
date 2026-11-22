import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0017
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0010
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBFr
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqPf
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GaugeR

def ExpPowSt : Prop :=
  ∀ (S σ : Type) [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S), MvPowerSeries.constantCoeff q = 0 →
    ∀ k : ℕ, PowerSeries.subst q (PowerSeries.exp S) ^ k * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S) = 1

theorem gaugeUniq_of' (hB : BetaUniqSt) (hR : GaugeRatioSt) (hP : ExpPowSt) : GaugeUniqSt := by
  intro E _ _ _ H Dw l Xo c S _ _ _ y x hx e e' he he'
  have hL := Xo.univ.t.PP.isLB
  choose u hu using fun m => ratio_of_gen Xo.univ.t.PP.L hL (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ))
    (e m) (e' m) (he.gen m) (he'.gen m)
  let g : ∀ m, Jet S (Fin 1 × Fin (dL Dw)) m := fun m => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (u m).val
  have hpull : ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra S B] (f : Jet S (Fin 1 × Fin (dL Dw)) m →ₐ[S] B),
      gam B (pullUnit (homAt y.x f).left (u m)).val = f (g m) := fun m B _ _ f =>
    gam_pullUnit (f : Jet S (Fin 1 × Fin (dL Dw)) m →+* B) (u m)
  have htr : ∀ m, jetTrunc (g (m + 1)) = g m := by
    intro m
    have h1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] _)).left (hu (m + 1))
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (hu m) (he.trunc m) (he'.trunc m)
    have h2 := congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU
    exact (hpull (m + 1) _ jetTrunc).symm.trans h2
  obtain ⟨r, hr⟩ := exists_ps_of_compat g htr
  have hrig : MvPowerSeries.constantCoeff r = 1 := by
    have h1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left (hu 0)
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (scaled_one _) he.rig he'.rig
    have h2 := congrArg (fun v => gam S (Units.val v)) hU
    simp only [Units.val_one, map_one] at h2
    rw [← jetAug_psJet 0 r, hr 0]
    exact (hpull 0 S jetAug).symm.trans h2
  have hid : ∀ a : 𝓞 E, MvPowerSeries.rescale (sc (Dw := Dw) c S (1 + a * H.bar a)) r =
      MvPowerSeries.rescale (sc (Dw := Dw) c S a) r ^ 2 * r *
        MvPowerSeries.rescale (sc (Dw := Dw) c S (a * H.bar a)) r := by
    intro a
    obtain ⟨β, hβg, hβr, hβc⟩ := he.coc a
    obtain ⟨β', hβ'g, hβ'r, hβ'c⟩ := he'.coc a
    obtain rfl := hB E H Dw l Xo a β β' hβg hβ'g hβr hβ'r
    refine GermFun.psJet_inj fun m => ?_
    have s1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (1 + a * H.bar a)))).left (hu m)
    have sa := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a))).left (hu m)
    have sb := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (a * H.bar a)))).left (hu m)
    have srhs := scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_one (LB.pullGen Xo.univ.t.PP.L _ _ β (x m).left))
      (scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_genPow _ _ sa 2) (scaled_mul Xo.univ.t.PP.L _ _ _ _ (hu m) sb))
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ s1 srhs (hβc m) (hβ'c m)
    have hv := congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, one_mul] at hv
    rw [hpull, hpull, hpull] at hv
    have hv' : jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (1 + a * H.bar a) i) * MvPolynomial.X i) (g m) =
        jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S a i) * MvPolynomial.X i) (g m) ^ 2 *
          (g m * jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (a * H.bar a) i) * MvPolynomial.X i) (g m)) :=
      hv
    rw [psJet_mul, psJet_mul, psJet_pow, ← jetSubstP_scale, ← jetSubstP_scale, ← jetSubstP_scale, hr m, hv']
    ring
  obtain ⟨q, hq0, hdeg, hpair, hexp⟩ := ratio_exp hR c S r hrig hid
  refine ⟨q, hq0, hdeg, hpair, fun k F f f' hf hf' => ?_⟩
  refine GermFun.psJet_inj fun m => ?_
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf m
  obtain ⟨F₂, τ₂, hP₂, hC₂, hV₂⟩ := hf' m
  have hF := GermFun.pull_unique _ _ _ _ _ _ _ _ hP₁ hP₂
  subst hF
  have sg := scaled_genPow (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ)) (hu m) k
  have sτ := corr_scaled_left Xo.univ.t.PP.L hL (x m).left (k : ℤ) _ _ τ₁ τ₂ _ _ _ sg hC₁ hC₂
  have hval := value_scaled Xo.univ.t.G Xo.univ.t.PP.L hL (k : ℤ) _ (x m) τ₁ τ₂ _ _ _ hV₁ hV₂ sτ
  have hg := congrArg (gam (Jet S (Fin 1 × Fin (dL Dw)) m)) hval
  rw [gam_toΓ, map_mul, gam_toΓ, Units.val_pow_eq_pow_val, map_pow] at hg
  have hpow := congrArg (psJet m) (hP S _ q hq0 k)
  rw [psJet_mul, psJet_pow, ← hexp, hr m, psJet_one] at hpow
  rw [psJet_mul, hg]
  calc psJet m f' = psJet m f' * (g m ^ k * psJet m (PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S))) := by
        rw [hpow, mul_one]
    _ = _ := by ring

end GaugeR

theorem gaugeUniq_of (hB : BetaUniqSt) : GaugeUniqSt :=
  GaugeR.gaugeUniq_of' hB GRPf.gaugeRatio fun _ _ _ _ q hq k => GaugeR.exp_pow_mul_exp_neg q hq k

theorem gaugeUniq_of_global (hG : GlobalFnsSt) : GaugeUniqSt :=
  gaugeUniq_of (betaUniq_of_global hG)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

attribute [local instance] Over.cartesianMonoidalCategory

section JetSubst

variable {S : Type} [CommRing S] {κ κ' : Type}

theorem jetSubstP_congr (m : ℕ) (φ ψ : κ → MvPolynomial κ' S) (h : ∀ i, φ i - ψ i ∈ orig S κ' ^ (m + 1)) :
    (jetSubstP m φ : Jet S κ m →ₐ[S] Jet S κ' m) = jetSubstP m ψ := by
  unfold jetSubstP jetMap
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  rw [Ideal.Quotient.eq]
  have hc : MvPolynomial.constantCoeff (φ i) = MvPolynomial.constantCoeff (ψ i) := by
    have h1 : φ i - ψ i ∈ orig S κ' := Ideal.pow_le_self (Nat.succ_ne_zero m) (h i)
    have h2 : orig S κ' ≤ RingHom.ker (MvPolynomial.constantCoeff (R := S) (σ := κ')) := by
      unfold orig
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simp
    have h3 := h2 h1
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h3
    exact h3
  rw [hc]
  convert h i using 1
  ring

theorem jetSubstP_trunc (m : ℕ) (φ : κ → MvPolynomial κ' S) :
    (jetTrunc : Jet S κ' (m + 1) →ₐ[S] Jet S κ' m).comp (jetSubstP (m + 1) φ) =
      (jetSubstP m φ).comp (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m) := by
  unfold jetSubstP jetMap jetTrunc liftJet
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  rfl

theorem rename_mem_orig_pow {κ'' : Type} (f : κ' → κ'') (n : ℕ) {p : MvPolynomial κ' S} (hp : p ∈ orig S κ' ^ n) :
    MvPolynomial.rename f p ∈ orig S κ'' ^ n := by
  have hle : Ideal.map (MvPolynomial.rename f : MvPolynomial κ' S →ₐ[S] MvPolynomial κ'' S) (orig S κ') ≤
      orig S κ'' := by
    unfold orig
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨f j, (MvPolynomial.rename_X f j).symm⟩
  have hm := Ideal.mem_map_of_mem (MvPolynomial.rename f : MvPolynomial κ' S →ₐ[S] MvPolynomial κ'' S) hp
  rw [Ideal.map_pow] at hm
  exact Ideal.pow_right_mono hle n hm

theorem psIn_succ_sub {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (g : MvPowerSeries (Fin n × Fin d) S) :
    psIn d (m + 1) r g - psIn d m r g ∈ orig S (Fin n' × Fin d) ^ (m + 1) := by
  unfold psIn
  rw [← map_sub]
  apply rename_mem_orig_pow
  unfold psTrunc
  have memD : ∀ (k : ℕ) (e : (Fin n × Fin d) →₀ ℕ),
      e ∈ (degLE k : Finset ((Fin n × Fin d) →₀ ℕ)) ↔ (e.sum fun _ a => a) ≤ k := by
    intro k e
    unfold degLE
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      refine ⟨⟨fun i => ⟨e i, ?_⟩, ?_⟩, h⟩
      · have hle : e i ≤ e.sum fun _ a => a := by
          rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
          exact Finset.single_le_sum (f := fun j => e j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      · ext i
        simp
  have monoMem : ∀ (k : ℕ) (e : (Fin n × Fin d) →₀ ℕ) (c : S), k ≤ (e.sum fun _ a => a) →
      MvPolynomial.monomial e c ∈ orig S (Fin n × Fin d) ^ k := by
    intro k e c hk
    have hmem : (e.prod fun i a => MvPolynomial.X i ^ a) ∈ orig S (Fin n × Fin d) ^ (e.sum fun _ a => a) := by
      simp only [Finsupp.prod, Finsupp.sum]
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Ideal.prod_mem_prod
      intro i _
      apply Ideal.pow_mem_pow
      unfold orig
      exact Ideal.subset_span ⟨i, rfl⟩
    rw [MvPolynomial.monomial_eq]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hk hmem)
  have hsub : (degLE m : Finset ((Fin n × Fin d) →₀ ℕ)) ⊆ degLE (m + 1) := by
    intro e he
    rw [memD] at he ⊢
    omega
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  apply Ideal.sum_mem
  intro e he
  rw [Finset.mem_sdiff, memD, memD] at he
  apply monoMem
  omega

end JetSubst

section Series

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)

theorem val_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι)
    (hJ : Good t.PP.L z J) : val (scaleGenG t φ ε u g) r z J = gm r z ⊤ u * val g r z J := by
  unfold scaleGenG val gm
  have hz : r z ∈ t.PP.L.wchart φ fun k => J (r ≫ φ k) := by
    unfold Good at hJ
    unfold LB.wchart
    show r z ∈ (⋂ k, ⇑(φ k) ⁻¹' ↑(t.PP.L.U (J (r ≫ φ k))) : Set _)
    rw [Set.mem_iInter]
    intro k
    have hk := hJ (r ≫ φ k)
    simpa using hk
  rw [dif_pos hz, dif_pos (show r z ∈ (⊤ : Y.Opens) from trivial)]
  dsimp only
  refine (MonoidHom.map_mul _ _ _).trans ?_
  congr 1
  apply Units.ext
  unfold pullU res
  have hz' : z ∈ r ⁻¹ᵁ (t.PP.L.wchart φ fun k => J (r ≫ φ k)) := hz
  have ht : z ∈ r ⁻¹ᵁ (⊤ : Y.Opens) := trivial
  have key := congrArg (fun f => CommRingCat.Hom.hom f (u : Γ(Y, ⊤)))
    (show Y.presheaf.map (homOfLE (le_top : t.PP.L.wchart φ (fun k => J (r ≫ φ k)) ≤ ⊤)).op ≫
        Scheme.Hom.app r (t.PP.L.wchart φ fun k => J (r ≫ φ k)) ≫
        Z.presheaf.germ (r ⁻¹ᵁ t.PP.L.wchart φ fun k => J (r ≫ φ k)) z hz' =
        Scheme.Hom.app r ⊤ ≫ Z.presheaf.germ (r ⁻¹ᵁ ⊤) z ht by
      rw [Scheme.Hom.naturality_assoc, TopCat.Presheaf.germ_res]
      all_goals rfl)
  first
    | exact key
    | (simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key
       simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
       exact key)

abbrev ρn (n m : ℕ) : jOG x0 d m n ⟶ jOG x0 d (m + 1) n :=
  homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] Jet S (Fin n × Fin d) m)

theorem exists_series {n : ℕ} {K K' : Type} [Fintype K] [Fintype K']
    (φ : ∀ m, K → ((jOG x0 d m n).left ⟶ t.G.left)) (ε : K → ℤ)
    (φ' : ∀ m, K' → ((jOG x0 d m n).left ⟶ t.G.left)) (ε' : K' → ℤ)
    (A : ∀ m, LB.Gen (LB.LinComb t.PP.L (φ m) ε)) (hA : ∀ m, (A m).IsGen)
    (B : ∀ m, LB.Gen (LB.LinComb t.PP.L (φ' m) ε')) (hB : ∀ m, (B m).IsGen)
    (hF : ∀ m, FormEq (φ m) ε (φ' m) ε')
    (hAt : ∀ m y J, Good t.PP.L y J → val (A (m + 1)) (ρn x0 d n m).left y J = val (A m) (𝟙 _) y J)
    (hBt : ∀ m y J, Good t.PP.L y J → val (B (m + 1)) (ρn x0 d n m).left y J = val (B m) (𝟙 _) y J) :
    ∃ ph : MvPowerSeries (Fin n × Fin d) S, ∀ m, ∃ u : (Jet S (Fin n × Fin d) m)ˣ,
      (u : Jet S (Fin n × Fin d) m) = psJet m ph ∧
      LB.Gen.Corr t.PP.L _ _ _ _ (A m) (scaleGenG t _ _ (unitΓ u) (B m)) := by
  have hL := t.PP.isLB
  choose U hU using fun m => exists_ratio t.PP.L hL (hF m) (A m) (hA m) (B m) (hB m)
  have hv : ∀ m, ∃ v : (Jet S (Fin n × Fin d) m)ˣ, unitΓ v = U m := fun m =>
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin n × Fin d) m))).hom.hom.toMonoidHom (U m),
      Units.ext (congrArg (fun f => CommRingCat.Hom.hom f (U m).val)
        (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin n × Fin d) m)))))⟩
  choose v hv using hv
  have hUc : ∀ m, U m = pullU (ρn x0 d n m).left ⊤ (U (m + 1)) := by
    intro m
    refine unit_ext (V := ⊤) fun y _ => ?_
    choose I hI using fun χ : (jOG x0 d m n).left ⟶ t.G.left => exists_chart hL (χ y)
    have e1 := hU m _ (𝟙 _) y I hI
    have e2 := hU (m + 1) _ (ρn x0 d n m).left y I hI
    have e3 := gm_pull (𝟙 _) (ρn x0 d n m).left y ⊤ trivial (U (m + 1))
    rw [Category.id_comp] at e3
    refine Eq.trans ?_ e3.symm
    exact (mul_inv_eq_iff_eq_mul.2 e1).symm.trans ((congrArg₂ (fun a b => a * b⁻¹) (hAt m y I hI).symm
      (hBt m y I hI).symm).trans (mul_inv_eq_iff_eq_mul.2 e2))
  have hac : ∀ m, (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) (v (m + 1)) = v m := by
    intro m
    apply toΓ_injective
    have e1 := congrArg Units.val (hv m)
    have e2 := congrArg Units.val (hv (m + 1))
    have nat := congrArg (fun f => CommRingCat.Hom.hom f ((v (m + 1) : Jet S (Fin n × Fin d) (m + 1))))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) :
        Jet S (Fin n × Fin d) (m + 1) →+* Jet S (Fin n × Fin d) m)))
    refine nat.trans (Eq.trans ?_ e1.symm)
    refine (congrArg (fun a => ((ρn x0 d n m).left.appTop).hom a) e2).trans ?_
    rw [hUc m]
    rfl
  obtain ⟨ph, hph⟩ := exists_ps_of_jets (fun m => (v m : Jet S (Fin n × Fin d) m)) hac
  refine ⟨ph, fun m => ⟨v m, (hph m).symm, corr_of_val hL fun y J hJ => ?_⟩⟩
  exact (hU m _ (𝟙 _) y J hJ).trans ((congrArg (fun u => gm (𝟙 _) y ⊤ u * val (B m) (𝟙 _) y J) (hv m).symm).trans
    (val_scale t _ _ _ _ _ y J hJ).symm)

theorem pe_trunc {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {e : ∀ m, FrTyG t x0 d x m} (htr : FrTrunc t x0 d x e) {n : ℕ}
    (φ : ℕ → Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (hφ : ∀ m i j, φ (m + 1) i j - φ m i j ∈ orig S (Fin n × Fin d) ^ (m + 1))
    (m : ℕ) (y : (jOG x0 d m n).left) (J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι) (hJ : Good t.PP.L y J) :
    val (peG t x0 d x e (m + 1) (φ (m + 1))) (ρn x0 d n m).left y J = val (peG t x0 d x e m (φ m)) (𝟙 _) y J := by
  have hc : (jetSubstP m fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2 :
      Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) = jetSubstP m fun p => φ m p.1 p.2 :=
    jetSubstP_congr m _ _ (fun p => hφ m p.1 p.2)
  have hcomp : (ρn x0 d n m).left ≫
      (homAt x0 (jetSubstP (m + 1) fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2)).left =
      (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2)).left ≫
        (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left := by
    rw [← Over.comp_left, ← Over.comp_left, homAt_comp, homAt_comp, jetSubstP_trunc]
  unfold peG
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ (e (m + 1))
    (homAt x0 (jetSubstP (m + 1) fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2)).left (ρn x0 d n m).left (z := y) (J := J)
  have h2 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ (e m)
    (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left (𝟙 _) (z := y) (J := J)
  have h3 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ (e (m + 1))
    (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left
    (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left (z := y) (J := J)
  have h4 : val (LB.pullGen t.PP.L _ _ (e (m + 1))
      (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
      (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left y J =
      val (e m) (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left y J := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr (htr m) _
    | exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr hJ (htr m) _
    | exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr (htr m) _ hJ
  try unfold peG
  refine h1.trans ?_
  rw [hcomp, hc]
  refine h3.symm.trans (h4.trans ?_)
  refine (h2.trans ?_).symm
  rw [Category.id_comp]

end Series

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.LemmaBFSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

def LemmaBFSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →

  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup →
    ¬ IsUnit ((g : ℕ) : T.V) →

    (letI := io.toAlgebra; ∀ e : Fin 2 × Fin (chD C.ch) →₀ ℕ, e.degree < g →
      MvPowerSeries.coeff e C.ch.h ∈ (algebraMap T.V T.Fr).range) →

  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →

  ∀ (O : Type) [CommRing O] [Algebra O F] [Algebra T.V O] [IsScalarTower T.V O F],
    Function.Injective (algebraMap O F) → (∀ z : F, 0 ≤ v z ↔ z ∈ (algebraMap O F).range) →
    IsAdicComplete (Ideal.span {((g : ℕ) : O)}) O →
    ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a)
        (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))),

  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →

  ∀ (n₁ n₂ : ℕ), 1 ≤ n₁ + n₂ → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre (n₁ + n₂))
    (pA : IsPowPolAV A' P.A (n₁ + n₂)) (pG : IsPowGrp G' C.I.G.G (n₁ + n₂))
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin (n₁ + n₂)), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin (n₁ + n₂)),
      oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
    TraceFormTwistIso D'.toPre oD' H.w0 →

  ∀ (m : (E →+* ℂ) → ℕ → ℕ),
    (∀ τ s, m τ s ≠ 0 → 1 ≤ s ∧ s ≤ Dw.mult τ ∧
      s ≤ (if 0 < v (algebraMap T.Fr F (io (embK c τ (star π)))) then n₁ else n₂)) →
    degOf Dw m < g - 1 → 4 * degOf Dw m + 4 ≤ g' → (degOf Dw m : ℝ) * M0 < g' →
  ∀ (ρg : ℚ), v ((g : ℕ) : F) = (ρg : WithTop ℚ) →
    letI := io.toAlgebra
    ∃ (s : Fam D'.toPre F g') (s₂ : Fam D'.toPre F (g' * g)) (p : QkPt D'.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (g' * g))
      (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F (n₁ + n₂) (chD C.ch)) (ρ : ℚ),
      NuGe D' (sumQ pD.xe Q) F v g' s 0 ∧
      PullAl D' F oD' (star π) g' g s s₂ ∧
      (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D' F (g' * g) p w ζ) ∧
      QkToAkU U'.toUnifPre F (g' * g) p x ∧ (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) ∧
      PhiRel D'.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
      U'.toUnifPre.ExpandsG F (g' * g) σ' t ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h ∧
      v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h
          (fun ℓ : LtN Dw (n₁ + n₂) => ℓ.2.2) (fun (ℓ : LtN Dw (n₁ + n₂)) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
          (minorProd Dw F (fun τ => 0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) m n₁
              (fun i => Fin.castAdd n₂ i) *
            minorProd Dw F (fun τ => ¬ 0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) m n₂
              (fun i => Fin.natAdd n₁ i))) = (ρ : WithTop ℚ) ∧
      (ρ : ℝ) ≤ (ρg : ℝ) * degOf Dw m / (g - 1) + n₁ * r * Φ / (4 * g') + 2 * degOf Dw m ^ 2 * Φ / g'

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

