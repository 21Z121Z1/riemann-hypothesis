import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceBoundSplitOfIntegral
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

section Val

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {la : HeightOneSpectrum R} {V : Type} {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K'] [Algebra V K'] [IsFractionRing V K']

theorem nval_nonneg_of_int (e : ℕ) {x : K'} (hx : x ∈ (algebraMap V K').range) : 0 ≤ nval V e x := by
  unfold nval
  split_ifs with h0
  · exact le_top
  · obtain ⟨y, rfl⟩ := hx
    unfold vV
    have hv : valV V ((algebraMap V K') y) ≤ 1 := by
      unfold valV
      exact HeightOneSpectrum.valuation_le_one _ y
    have hne : valV V ((algebraMap V K') y) ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
    have hl : ((valV V) ((algebraMap V K') y)).log ≤ 0 := by
      first
      | exact (WithZero.log_le_log hne one_ne_zero).mpr hv |>.trans_eq WithZero.log_one
      | exact WithZero.log_nonpos hv
      | exact WithZero.log_le_zero_iff.mpr hv
      | simpa using WithZero.log_mono hne hv
    have h1 : (0:ℝ) ≤ ((-(valV V ((algebraMap V K') y)).log : ℤ) : ℝ) / (e : ℝ) :=
      div_nonneg (by exact_mod_cast (by omega : (0:ℤ) ≤ -(valV V ((algebraMap V K') y)).log)) (Nat.cast_nonneg _)
    exact EReal.coe_nonneg.mpr h1

theorem nval_pow_smul {ι : K →+* K'} {e : ℕ} (ho : OverLa la V ι e) {a : K} (ha : a ≠ 0) (n : ℕ) (x : K') :
    nval V e (ι a ^ n * x) = ((((n : ℤ) * vLa la a : ℤ) : ℝ) : EReal) + nval V e x := by
  obtain ⟨he, hv⟩ := ho
  have hιa : ι a ≠ 0 := (map_ne_zero ι).2 ha
  by_cases hx : x = 0
  · subst hx
    unfold nval
    rw [mul_zero, if_pos rfl]
    exact (EReal.coe_add_top _).symm
  · have hprod : ι a ^ n * x ≠ 0 := mul_ne_zero (pow_ne_zero _ hιa) hx
    have hva : valV V (ι a) ≠ 0 := (Valuation.ne_zero_iff _).mpr hιa
    have hvx : valV V x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    have hmul : vV V (ι a ^ n * x) = n * vV V (ι a) + vV V x := by
      unfold vV
      rw [map_mul, map_pow]
      first
      | (rw [WithZero.log_mul (pow_ne_zero _ hva) hvx, WithZero.log_pow]; ring)
      | (rw [WithZero.log_mul (pow_ne_zero _ hva) hvx, WithZero.log_pow]; push_cast; ring)
      | (simp [WithZero.log_mul, WithZero.log_pow, hva, hvx]; ring)
    unfold nval
    rw [if_neg hprod, if_neg hx, hmul, hv a, ← EReal.coe_add]
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    congr 1
    push_cast
    field_simp

theorem neg_le_nval_of_mem {ι : K →+* K'} {e : ℕ} (ho : OverLa la V ι e) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (p m : ℕ) (x : K') (hx : ι a ^ p * (ι b ^ m * x) ∈ (algebraMap V K').range) :
    (((-(((vLa la a : ℤ) : ℝ) * (p : ℝ) + ((vLa la b : ℤ) : ℝ) * (m : ℝ))) : ℝ) : EReal) ≤ nval V e x := by
  have h0 := nval_nonneg_of_int e hx
  rw [nval_pow_smul ho ha, nval_pow_smul ho hb] at h0
  by_cases hx0 : x = 0
  · subst hx0
    unfold nval
    simp
  · have hN : nval V e x = ((((vV V x : ℤ) : ℝ) / (e : ℝ) : ℝ) : EReal) := by
      unfold nval
      rw [if_neg hx0]
    rw [hN] at h0 ⊢
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_nonneg] at h0
    rw [EReal.coe_le_coe_iff]
    push_cast at h0 ⊢
    linarith

end Val

def NnIntCSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) → ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ∀ (i : Fin 2) (πE : 𝓞 D.host.E) (τ : D.host.E →+* ℂ),
      InPsi T.Q.H τ → πE * T.Q.H.bar πE = (D.host.g i : 𝓞 D.host.E) →
      T.Q.l.Mb ≤ Ideal.span {T.Q.H.bar πE} → ((D.host.g i : 𝓞 T.Q.c.F) ∈ la.asIdeal) → D.host.g i ≠ D.host.q →
      io (embK T.Q.c τ πE) ^ (∑ t, ∑ k, w.aP t k) *
        (io (embK T.Q.c τ (T.Q.H.bar πE)) ^ (∑ t, ∑ k, w.aM t k) * evI yI f) ∈ (algebraMap Tc.V Tc.Fr).range

theorem place_bound_split_of_integral (hI : NnIntCSt) : PlaceBoundSplitPrime := by
  intro D T h j hj nab hadm w x P hP f hf la y i πE τ hτ hπ hM hg hgq
  obtain ⟨Tc, io, e, ho, yI, hy, eta, heta, hq⟩ := y.2
  have hv : vAtV y f = nval Tc.V e (evI yI f) := by
    show y.1.1 f = _
    rw [hq]
    rfl
  rw [hv]
  have hgi : (D.host.g i : 𝓞 D.host.E) ≠ 0 := by
    intro h0
    have h1 := congrArg (algebraMap (𝓞 D.host.E) D.host.E) h0
    simp only [map_natCast, map_zero, Nat.cast_eq_zero] at h1
    exact (D.host.g_prime i).ne_zero h1
  have hπ0 : πE ≠ 0 := by
    rintro rfl
    exact hgi (by rw [← hπ, zero_mul])
  have hπb0 : T.Q.H.bar πE ≠ 0 := by
    intro h0
    exact hgi (by rw [← hπ, h0, mul_zero])
  have hemb : ∀ a : 𝓞 D.host.E, a ≠ 0 → embK T.Q.c τ a ≠ 0 := by
    intro a ha h0
    have h1 := embK_coe T.Q.c τ a
    rw [h0] at h1
    have h2 : τ (a : D.host.E) = 0 := by rw [← h1]; simp
    have h3 : (a : D.host.E) = 0 := (map_eq_zero τ).1 h2
    exact ha (RingOfIntegers.coe_injective (by simpa using h3))
  exact neg_le_nval_of_mem ho (hemb πE hπ0) (hemb _ hπb0) _ _ _
    (hI D T h j hj nab hadm w x P hP f hf Tc io yI e la ho hy i πE τ hτ hπ hM hg hgq)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SubMulPf
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem lieFacAdd : LieFacAddSt := by
  intro E _ _ _ H Dw x a a'
  simp only [Formalism.L2.Pj.lieFac, ← Real.exp_add]
  congr 1
  simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
  ring

theorem pnormMul : PnormMulSt := by
  intro E _ _ _ r X la la' P Q x hx
  have hne : ∀ τ j, ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ j ≠ 0 := fun τ j h => by
    have h1 := (hx τ).2 j
    rw [h, Complex.zero_re, mul_zero] at h1
    exact lt_irrefl 0 h1
  have hpos : ∀ τ (i : Fin r), 0 < ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ /
      ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ := fun τ i =>
    norm_pos_iff.2 (div_ne_zero (hne τ _) (hne τ _))
  have key : ∀ τ (i : Fin r), ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ /
      ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^ (-((la + la') τ i : ℝ) / 2) =
      ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^
          (-(la τ i : ℝ) / 2) *
        ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^
          (-(la' τ i : ℝ) / 2) := fun τ i => by
    rw [← Real.rpow_add (hpos τ i)]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    ring
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  rw [Pi.mul_apply, norm_mul]
  simp only [key, Finset.prod_mul_distrib]
  ring

theorem pnorm_nonneg' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : 0 ≤ X.pnorm la P x :=
  mul_nonneg (norm_nonneg _) (Formalism.L2.Pj.pnorm_fac_nonneg X la x)

theorem supCMul : SupCMulSt := by
  intro E _ _ _ H Dw l Xo c r U x σ a a' n n' f g _ hn hn' hf hg
  unfold supC
  rw [lieFacAdd E H Dw x a a', rdU_mul]
  have hla : laU (U σ) (a + a') (n + n') = laU (U σ) a n + laU (U σ) a' n' :=
    funext fun k => laU_add (U σ) a a' n n' hn hn' k
  rw [hla]
  have hE : Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n + laU (U σ) a' n') (rdU (U σ) f * rdU (U σ) g) ≤
      Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) *
        Formalism.L2.Pj.supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g) := by
    unfold Formalism.L2.Pj.supE
    refine iSup_le fun p => ?_
    have e := pnormMul E r ((U σ).X p.1) (laU (U σ) a n p.1) (laU (U σ) a' n' p.1) (rdU (U σ) f p.1)
      (rdU (U σ) g p.1) p.2.1 p.2.2
    refine le_trans (le_of_eq ?_) (mul_le_mul' (le_iSup (fun q : FPt (U σ).X =>
      ENNReal.ofReal (((U σ).X q.1).pnorm (laU (U σ) a n q.1) (rdU (U σ) f q.1) q.2)) p)
      (le_iSup (fun q : FPt (U σ).X =>
      ENNReal.ofReal (((U σ).X q.1).pnorm (laU (U σ) a' n' q.1) (rdU (U σ) g q.1) q.2)) p))
    rw [← ENNReal.ofReal_mul (pnorm_nonneg' _ _ _ _)]
    exact congrArg ENNReal.ofReal e
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top hf hg) hE
  rw [ENNReal.toReal_mul] at h1
  unfold Formalism.L2.Pj.supN
  calc lieFac Dw x a * lieFac Dw x a' *
        (Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n + laU (U σ) a' n') (rdU (U σ) f * rdU (U σ) g)).toReal
      ≤ lieFac Dw x a * lieFac Dw x a' * ((Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n) (rdU (U σ) f)).toReal *
          (Formalism.L2.Pj.supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g)).toReal) :=
        mul_le_mul_of_nonneg_left h1 (mul_pos (lieFac_pos _ _ _) (lieFac_pos _ _ _)).le
    _ = _ := by ring

theorem recSubMul : RecSubMulSt := by
  intro D T h j hj σ w w' F G H hH
  have hFm : (F : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := cutR_le T.C j w F.2
  have hGm : (G : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w') w'.n := cutR_le T.C j w' G.2
  have hprod : (H : T.R j) = (F : T.R j) * (G : T.R j) := by
    have h1 := congrArg (fun x : AddMonoidAlgebra (T.R j) (Deg D j) => x.coeff (deg (Formalism.MainNotions.WeightAlgebra.wadd w w'))) hH
    change (incG deg (cutR T.C j) (Formalism.MainNotions.WeightAlgebra.wadd w w') H).coeff _ =
      (incG deg (cutR T.C j) w F * incG deg (cutR T.C j) w' G).coeff _ at h1
    rw [incG_apply, incG_apply, incG_apply, AddMonoidAlgebra.single_mul_single, ← deg_wadd] at h1
    simpa [AddMonoidAlgebra.coeff_single] using h1
  show cutN T.C T.Ns j (Formalism.MainNotions.WeightAlgebra.wadd w w') σ H ≤ cutN T.C T.Ns j w σ F * cutN T.C T.Ns j w' σ G
  unfold cutN
  rw [if_pos hj, if_pos hj, if_pos hj]
  unfold Core.Ns
  rw [hprod, wtA_wadd]
  exact supCMul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (goodEmb_goodOf _ σ) w.n_even w'.n_even
    (supE_cusp_ne_top (goodEmb_goodOf _ σ) hFm) (supE_cusp_ne_top (goodEmb_goodOf _ σ) hGm)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TanAddPf
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem tanAdd_holds (Xo : Moduli Dw l) : TanAddSt Xo := by
  intro S _ x w hw a b u₁ u₂ h₁ h₂
  have e₁ : u₁ = smT x a (ovT (t := Xo.univ.t) hw) := Over.OverMorphism.ext h₁
  have e₂ : u₂ = smT x b (ovT (t := Xo.univ.t) hw) := Over.OverMorphism.ext h₂
  rw [e₁, e₂, ← smT_add x _ (smT_zero_ovT hw)]
  rfl

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def vspActL {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) :
    ReciprocityTheory.ChartRestriction.G.I2.Vsp dim →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp dim where
  toFun := ReciprocityTheory.ChartRestriction.G.I2.act α
  map_add' v w := by
    ext i
    simp [ReciprocityTheory.ChartRestriction.G.I2.act, mul_add]
  map_smul' c v := by
    ext i
    simp [ReciprocityTheory.ChartRestriction.G.I2.act]
    ring

def ThetaValCAlphaSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) →
    ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom),
    (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) →
    ∀ (W : UnfAt (T.U j σ) k xf) (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) xf.1)
      (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim),
    TorusPins W Wu A L →
    ∀ (α : 𝓞 D.host.E), α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) → T.Q.l.Mb = Ideal.span {T.Q.H.bar α} →
    ∀ (x2 : Fin w.n → (T.Q.Dw j).La),
      (∀ b, x2 b ∈ (Ideal.span {(2 : 𝓞 D.host.E)} *
          (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) ^ 2) •
            (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)) →
      (∀ b, x2 b - x b ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)) →
      σ (∏ τ : D.host.E →+* ℂ, (embK T.Q.c τ α) ^ (∑ i : Fin ((T.Q.Dw j).mult τ), wtA w (τ, i.1))) *
          toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf)) =
        star (ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.map ((starRingEnd ℂ).comp σ) P)
          (fun l => Pi.single l.2.2 (L (Pi.single (W.e.symm ⟨l.1, l.2.1⟩) 1)))
          (A.T.U T.Q.l.M (fun b => -((((T.Q.l.M : ℂ) ^ 2)⁻¹) •
            L (star (W.Pm (W.F.t (W.ik k) (T.Q.H.bar α • x2 b))))))
            (ReciprocityTheory.ChartRestriction.G.I2.s0 A.T (vspActL α) A.s)) 0)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCSteps
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

section FrRd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def IsFrRd {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) (Wu : UnitAt W) (kk : ℤ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L kk (Over.mk (U.un k x).x))) (θF : (Fin W.g → ℂ) → ℂ) : Prop :=
  ∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
    pt ≫ gxFst (U.un k x).x = (W.F.ex (W.ik k) W.Pm z).left →
    pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
    ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' pt ((LPow Xo.univ.t.G Xo.univ.t.PP.L kk (Over.mk (U.un k x).x)).U (fun _ => j))
      (F.f (fun _ => j)) = θF z * Wu.fr j z ^ kk

end FrRd

def VtFrRdSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j)
    (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom),
    (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) →
    ∀ (W : UnfAt (T.U j σ) k xf) (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) xf.1)
      (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim),
    TorusPins W Wu A L →
    ∀ (x x2 : (T.Q.Dw j).La),
      x2 ∈ (Ideal.span {(2 : 𝓞 D.host.E)} *
          (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) ^ 2) •
            (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) →
      x2 - x ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) →
      ∀ F : LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
          (ptO (T.Q.Xo j) ((T.U j σ).un k xf).x)),
      IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2))
        ((T.U j σ).un k xf).s (levPt (T.Q.Xo j) ((T.U j σ).un k xf).x x) F →
      IsFrRd W Wu ((T.Q.l.M : ℤ) ^ 2) F (fun z =>
        star (A.T.U (T.Q.l.M ^ 2) (fun _ : Fin 1 => -((((T.Q.l.M : ℂ) ^ 2)⁻¹) • L (star (W.Pm (W.F.t (W.ik k) x2)))))
          (ReciprocityTheory.ChartRestriction.G.I2.s0 A.T ((T.Q.l.M : ℂ) • LinearMap.id) A.s) (fun _ => L (star z))))

section BC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def VtPullSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (S S' : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] [CommRing S'] [Algebra c.F S'] [Algebra ℚ S']
    (φ : S →ₐ[c.F] S') (x0 : Sp S ⟶ Xo.X)
    (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo x0)))
    (s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo (spMap (φ : S →+* S') ≫ x0)))),
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (Formalism.MainNotions.ModuliIntegralCharts.H1.ptBC (φ : S →+* S') x0 ▷ Xo.univ.t.G)
      (whiskerRight_snd _ _) s s' →
    ∀ (a : Dw.La)
      (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo x0)))
      (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo (spMap (φ : S →+* S') ≫ x0)))),
      IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) s (levPt Xo x0 a) F →
      IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2)
        (Formalism.MainNotions.ModuliIntegralCharts.H1.ptBC (φ : S →+* S') x0 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' →
      IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) s' (levPt Xo (spMap (φ : S →+* S') ≫ x0) a) F'

def VtUniqSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (x0 : Sp S ⟶ Xo.X)
    (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo x0))) (a : Dw.La)
    (F F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo x0))),
    IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) s (levPt Xo x0 a) F →
    IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) s (levPt Xo x0 a) F' → F = F'

def ThValDescSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y0 : FrPt Xo c S) (K : Type) [Field K] [Algebra c.F K]
      (φ : S →ₐ[c.F] K) (y : FrPt Xo c K), FrMap φ y0 y →
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
        ∀ v0 w, ThValAt Xo c nab y0 x P v0 → ThValAt Xo c nab y x P w → φ v0 = w

end BC

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

