import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0046
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0047
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0044
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0048
import Formalism.LocalToGlobal.ProjectiveLattices.TieGen

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

theorem formsEvR_inc (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) :
    formsEvR j hG hT Z ((recPlus h j hj).inc u F) = evC hG Z ((F : (recB h.toLawsCore).Cusp j u) : T.R j) :=
  formsEvR_single j hG hT Z _ _

theorem birAt_of_ev {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} (X : PJ D B P j) (N : ℕ) {wL : WeightFamilies.Wt D j}
    (w : Fin N → B.Cusp j wL) {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (ev : ∀ u : WeightFamilies.Wt D j, B.Cusp j u → Ω) (hev : ∀ u F, gF (X.inc u F) = ev u F)
    (hB : ∀ a : Ω, ∃ (k : ℕ) (g : B.Cusp j (wsmul k wL)) (Pw : MvPolynomial (Fin N) B.KO), Pw.IsHomogeneous k ∧
      MvPolynomial.aeval (fun i => ev wL (w i)) Pw ≠ 0 ∧
      a * MvPolynomial.aeval (fun i => ev wL (w i)) Pw = ev (wsmul k wL) g) :
    CurveLoc.BirAt X N w gF := by
  intro a
  obtain ⟨k, g, Pw, hP, hne, he⟩ := hB a
  refine ⟨k, g, Pw, hP, ?_, ?_⟩
  · simp only [hev]
    exact hne
  · simp only [hev]
    exact he

theorem birAt_of {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BIRSt h j hj hG G)
    (Z : Comp (T.Q.Xo j) T.Q.c) : CurveLoc.BirAt (recPlus h j hj) G.N G.w (formsEvR j hG hT Z) :=
  birAt_of_ev j (recPlus h j hj) G.N G.w (formsEvR j hG hT Z)
    (fun u F => evC hG Z ((F : (recB h.toLawsCore).Cusp j u) : T.R j))
    (fun u F => formsEvR_inc h j hj hG hT Z u F) (hB Z)

theorem split_of (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (Z : Comp (T.Q.Xo j) T.Q.c) (k : Fin G.N) :
    ∃ g : (recB h.toLawsCore).Cusp j wL,
      formsEvR j hG hT Z ((recPlus h j hj).inc wL g) = formsEvR j hG hT Z ((recPlus h j hj).inc wL (G.w k)) ∧
      ∀ Z', Z' ≠ Z → formsEvR j hG hT Z' ((recPlus h j hj).inc wL g) = 0 := by
  obtain ⟨g', h1, h2⟩ := hC Z wL (G.w k)
  exact ⟨g', by rw [formsEvR_inc, formsEvR_inc, h1], fun Z' hZ' => by rw [formsEvR_inc, h2 Z' hZ']⟩

def CountQAtSt : Prop :=
  ∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore))
    (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)),
    CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z : Comp (T.Q.Xo j) T.Q.c,
      CurveLoc.CountQAt (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)

theorem hone_of (hC : CompSplitSt h j hG) :
    ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
        ∀ Z Z', RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → RingHom.ker (phiI h j hj hG hT la G Z') ≤ Q → Z = Z' := by
  intro ka wL wF G S g0 la _ Q hQ _ Z Z' hZ hZ'
  exact CurveLoc.one_of_split (recPlus h j hj) la G.N G.w (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    (fun Z k => split_of h j hj hG hT hC G Z k) Q hQ Z Z' hZ hZ'

theorem hloc_of (hB : ∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore))
      (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → BIRSt h j hj hG G)
    (hQ : CountQAtSt h j hj hG hT) :
    ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
        ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
          (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
            RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧
          phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a := by
  intro ka wL wF G S g0 la hH Z r
  exact CurveLoc.loc_of_bir (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
    (birAt_of h j hj hG hT G (hB ka wL wF G S g0 hH) Z) (hQ ka wL wF G S g0 la hH Z) r

theorem countQAtSt_holds : CountQAtSt h j hj hG hT := by
  intro ka wL wF G S g0 la hH Z
  obtain ⟨k₀, hk₀, htr⟩ := hH.2.1.2 Z
  exact CurveLoc.countQAt_of (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
    (fun i => evC hG Z ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j))
    (fun i => formsEvR_inc h j hj hG hT Z wL (G.w i)) ⟨k₀, hk₀, le_of_eq htr⟩

theorem hloc_of_bir (hB : ∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore))
      (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → BIRSt h j hj hG G) :
    ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
        ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
          (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
            RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧
          phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a :=
  hloc_of h j hj hG hT hB (countQAtSt_holds h j hj hG hT)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FnDefC
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem relab_injective (c : Coeff l) (σ : c.F →+* ℂ) : Function.Injective (relab c σ) := by
  intro τ₁ τ₂ h
  ext a
  have := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective this)

theorem relab_rt_iff (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (τ' : E →+* ℂ) :
    relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0 := by
  have h0 : H.rt0 ≠ 0 := by
    intro h
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    have hd : (H.d : ℂ) = 0 := by linear_combination this
    exact H.d_prime.ne_zero (by exact_mod_cast hd)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
    simpa using this
  have hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE, map_neg, map_natCast]
  have hval : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩ := rfl
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hx | hx
  · refine ⟨fun _ => hx, fun _ => ?_⟩
    rw [hval, ← hσ0]
    exact congrArg σ (Subtype.ext hx)
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · exfalso
      have h1 : σ ⟨τ' (H.rt : E), c.conj τ' _⟩ = -σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ := by
        rw [← map_neg]
        exact congrArg σ (Subtype.ext hx)
      rw [← hval, h, hσ0] at h1
      exact h0 (by linear_combination h1 / 2)
    · exfalso
      exact h0 (by linear_combination (h.symm.trans hx) / 2)

theorem conjEmb_conjEmb (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ :=
  RingHom.ext fun z => Complex.conj_conj (τ z)

variable {σ : c.F →+* ℂ}

open Classical in

def letCol (U : Unf Xo c σ r) (k : U.Comp)
    (hmP : ∀ τ', relab c σ τ' ∈ (U.X k).Ψ → Dw.mult τ' + (U.X k).p0 ≤ r)
    (hmQ : ∀ τ', relab c σ τ' ∉ (U.X k).Ψ → conjEmb (relab c σ τ') ∈ (U.X k).Ψ ∧ Dw.mult τ' ≤ (U.X k).p0)
    (b : Σ τ' : E →+* ℂ, Fin (Dw.mult τ')) : (U.X k).Ψ × Fin r :=
  if h : relab c σ b.1 ∈ (U.X k).Ψ then
    (⟨_, h⟩, ⟨(U.X k).p0 + b.2, by have := hmP _ h; have := b.2.isLt; omega⟩)
  else (⟨_, (hmQ _ h).1⟩, ⟨(U.X k).p0 - 1 - b.2, by have := (hmQ _ h).2; have := b.2.isLt; have := (U.X k).p0_le; omega⟩)

open Classical in

def aCol (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (k : U.Comp) (τ : (U.X k).Ψ) (j : Fin r) : ℝ :=
  if (U.X k).p0 ≤ (j : ℕ) then (a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) : ℝ)
  else -(a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℝ)

def nCol (U : Unf Xo c σ r) (n : ℕ) (k : U.Comp) (j : Fin r) : ℝ :=
  if (U.X k).p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℝ) else -((n / 2 : ℕ) : ℝ)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.GenSpecCut
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def SepXSt : Prop := IsSeparated Xo.s

def LocDomSt : Prop := ∀ P : Xo.XF c, IsDomain ((Xo.XF c).presheaf.stalk P)

def stkAlg (P : Xo.XF c) : Algebra c.F ((Xo.XF c).presheaf.stalk P) :=
  (Spec.preimage ((Xo.XF c).fromSpecStalk P ≫ strK)).hom.toAlgebra

def xStk (P : Xo.XF c) : Sp ((Xo.XF c).presheaf.stalk P) ⟶ Xo.X :=
  (Xo.XF c).fromSpecStalk P ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)

def LocFrSt : Prop :=
  ∀ P : Xo.XF c, letI := stkAlg Xo c P; ∃ y : FrPt Xo c ((Xo.XF c).presheaf.stalk P), y.x = xStk Xo c P

variable {Xo c}

variable (Xo c) in

def FrGenChartSt (hG : GenFrEx Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (m : Ideal p.R) [m.IsMaximal],
    ∃ (Z : Comp Xo c) (q : TRing c.F) (yq : FrPt Xo c q.R),
      (∃ (p' : TRing c.F) (lam : p.R →ₐ[c.F] p'.R) (a : q.R →ₐ[c.F] p'.R)
          (μ : p'.R →ₐ[c.F] Localization.AtPrime m) (y' : FrPt Xo c p'.R),
        FrMap lam y y' ∧ FrMap a yq y' ∧ μ.comp lam = locM c.F m) ∧
      ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra c.F Ω) (κ : Om Z →ₐ[c.F] Ω) (γ : q.R →ₐ[c.F] Ω)
        (w w₀ : FrPt Xo c Ω) (t : Ix Dw → Ωˣ),
        Function.Injective γ ∧ FrMap γ yq w ∧ FrMap κ (genFr hG Z) w₀ ∧ FrBor t w₀ w

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.NrmTieDef
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def nrmTieDefRd (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hA : AllTest Xo c)
    (hB : ∀ σ, GoodEmb c σ → BCEx Xo c σ) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) :
    Σ k : (U (goodOf c σ)).Comp, ((U (goodOf c σ)).X k).dom × (Ix Dw → (CAt (goodOf c σ))ˣ) :=
  (rdEx_of U hU hA hB σ y).choose

end Gen

section Rec

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)

variable {j} in

def NrmTieKC (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (ka : WeightFamilies.Wt D j)
    (pt : ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ), SupPtAt j (goodOf Tc.Q.c (sgOf P))) : Prop :=
  ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ) (F : (recB hL).Cusp j ka),
    nrmC fn (yP Z) (wtZ (wtA ka) ka.n) (valC h (wtA ka) ka.n (F : Tc.R j) Z) P =
      recNrm (Tc.U j (goodOf Tc.Q.c (sgOf P))) (xiR D) (wtA ka) ka.n (F : Tc.R j) (pt Z P).1 (pt Z P).2.1

def nrmTieDefPt (hj : InR D j) (hA : AllTest (Tc.Q.Xo j) Tc.Q.c)
    (hB : ∀ σ, GoodEmb Tc.Q.c σ → BCEx (Tc.Q.Xo j) Tc.Q.c σ) (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (hb : CBaseEx (Tc.Q.Xo j) Tc.Q.c h) (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ) :
    SupPtAt j (goodOf Tc.Q.c (sgOf P)) :=
  ⟨(nrmTieDefRd (Tc.U j) (hL.unf j hj) hA hB (sgOf P) (yPDef h hb Z P)).1,
    (nrmTieDefRd (Tc.U j) (hL.unf j hj) hA hB (sgOf P) (yPDef h hb Z P)).2.1⟩

end Rec

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.TieGenR
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

def RatAt (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp)
    (Z : Comp (T.Q.Xo j) T.Q.c) (x : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r) (P : Om Z →+* ℂ) : Prop :=
  ∀ (u : WeightFamilies.Wt D j) (F G' : (recB h.toLawsCore).Cusp j u), Even u.n →
    valC hG (wtA u) u.n G'.1 Z ≠ 0 →
    rdR h j F (κ Z) x = P (ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) (valC hG (wtA u) u.n F.1 Z)
      (valC hG (wtA u) u.n G'.1 Z)) * rdR h j G' (κ Z) x

def genR (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp)
    (Z : Comp (T.Q.Xo j) T.Q.c) : Set (Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r) :=
  {x | x ∈ ((T.U j T.σ₀).X (κ Z)).dom ∧ ∃ P ∈ ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) T.σ₀, RatAt h j hG κ Z x P}

open Classical in

def ptR (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp)
    (Z : Comp (T.Q.Xo j) T.Q.c) (hne : Nonempty (Om Z →+* ℂ)) (x : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r) :
    Om Z →+* ℂ :=
  if hx : x ∈ genR h j hG κ Z then hx.2.choose else hne.some

def RecogSt (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp)
    (yP : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P))) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (x : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r)
    (hx : x ∈ ((T.U j T.σ₀).X (κ Z)).dom) (P : Om Z →+* ℂ), P ∈ ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) T.σ₀ →
    RatAt h j hG κ Z x P → PtIs yP Z ((T.U j T.σ₀).un (κ Z) ⟨x, hx⟩) P

def GenDenseSt (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) : Prop :=
  ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ S : ℕ → Set (Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r),
    (∀ n, IsClosed (S n) ∧ interior (S n) = ∅) ∧
    ((T.U j T.σ₀).X (κ Z)).dom \ genR h j hG κ Z ⊆ ⋃ n, S n

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.TieReadingOf
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

variable {D : D7} {T : Top D}

structure RdData1 {j : ℕ} (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E)
    (fun Z => AC Z)) (Z : Comp (T.Q.Xo j) T.Q.c) (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) where
  Rg : Subring (AC Z)
  w_mem : ∀ i, d.w i Z ∈ Rg
  rd : Rg →+* (Frame X.Ψ D.R.r → ℂ)
  WE : AddSubgroup (WTZ D.host.E)
  wL_mem : d.wL ∈ WE
  wt : WE →+ Wt X.Ψ D.R.r

def TieRd1Props (h : LawsP T) {j : ℕ} (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) (Z : Comp (T.Q.Xo j) T.Q.c)
    (R : RdData1 d Z ((T.U j T.σ₀).X (κ Z))) : Prop :=
  (∀ G (hG : G ∈ R.WE), ∀ f (hf : f ∈ R.Rg), f ∈ AG Z G → ((T.U j T.σ₀).X (κ Z)).IsSec (R.wt ⟨G, hG⟩) (R.rd ⟨f, hf⟩)) ∧
  (∀ G, ∀ f (hf : f ∈ R.Rg), f ∈ AG Z G → (∀ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, R.rd ⟨f, hf⟩ x = 0) → f = 0) ∧
  (∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u), Even u.n → valC hG (wtA u) u.n F.1 Z ∈ R.Rg) ∧
  (∀ (u : WeightFamilies.Wt D j), Even u.n → wtZ (wtA u) u.n ∈ R.WE) ∧
  (∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (hF : valC hG (wtA u) u.n F.1 Z ∈ R.Rg),
    ∀ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, R.rd ⟨_, hF⟩ x = rdR h j F (κ Z) x) ∧
  ∀ (u : WeightFamilies.Wt D j) (hu : wtZ (wtA u) u.n ∈ R.WE), R.wt ⟨_, hu⟩ = laU (T.U j T.σ₀) (wtA u) u.n (κ Z)

def TieRd2Props {j : ℕ}
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    (Z : Comp (T.Q.Xo j) T.Q.c) {X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r} (R : RdData1 d Z X)
    (Gen : Set (Frame X.Ψ D.R.r)) (pt : Frame X.Ψ D.R.r → (Om Z →+* ℂ)) : Prop :=
  Gen ⊆ X.dom ∧ X.dom ⊆ closure Gen ∧
  (∀ x ∈ Gen, pt x ∈ PT (Ω := Om Z) T.σ₀) ∧ (∀ P ∈ PT (Ω := Om Z) T.σ₀, ∃ x ∈ Gen, pt x = P) ∧
  (∀ G (hG : G ∈ R.WE), ∀ f (hf : f ∈ R.Rg), f ∈ AG Z G → ∀ x ∈ Gen,
    X.pnorm (R.wt ⟨G, hG⟩) (R.rd ⟨f, hf⟩) x = d.nrm Z G f (pt x)) ∧
  (∀ x ∈ Gen, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ D.R.r, lact γ (rmul x b) ∈ Gen ∧ pt (lact γ (rmul x b)) = pt x) ∧
  (∀ x ∈ Gen, ∀ x' ∈ Gen, pt x = pt x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ D.R.r, x' = lact γ (rmul x b)) ∧
  (∀ x ∈ X.dom, ∀ P ∈ PT (Ω := Om Z) T.σ₀,
    (∀ G ∈ R.WE, ∀ f (hf : f ∈ R.Rg) g (hg : g ∈ R.Rg), f ∈ AG Z G → g ∈ AG Z G → g ≠ 0 →
      R.rd ⟨f, hf⟩ x = P (ratio (Ω := Om Z) f g) * R.rd ⟨g, hg⟩ x) → x ∈ Gen ∧ pt x = P) ∧
  ∀ G, ∀ f (hf : f ∈ R.Rg) g (hg : g ∈ R.Rg), f ∈ AG Z G → g ∈ AG Z G → g ≠ 0 → ∀ x ∈ Gen,
    R.rd ⟨f, hf⟩ x = pt x (ratio (Ω := Om Z) f g) * R.rd ⟨g, hg⟩ x

def TieRd3Props {j : ℕ}
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    (Z : Comp (T.Q.Xo j) T.Q.c) {X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r} (R : RdData1 d Z X) : Prop :=
  (∀ a : Om Z, ∃ (G : WTZ D.host.E) (f p : AC Z), f ∈ R.Rg ∧ p ∈ R.Rg ∧ f ∈ AG Z G ∧ p ∈ AG Z G ∧ p ≠ 0 ∧
    p ∈ Algebra.adjoin T.Q.c.F (Set.range fun i => d.w i Z) ∧ a = ratio (Ω := Om Z) f p) ∧
  ∀ x ∈ X.dom, ∃ i, R.rd ⟨d.w i Z, R.w_mem i⟩ x ≠ 0

def TieRd4Props {j : ℕ}
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    (Z : Comp (T.Q.Xo j) T.Q.c) {X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r} (R : RdData1 d Z X)
    (Gen : Set (Frame X.Ψ D.R.r)) : Prop :=
  ∀ x ∈ Gen, ∃ (j0 : Fin (d.N + 1)) (jj : Fin (nd X) → Fin (d.N + 1)),
    R.rd ⟨d.w j0 Z, R.w_mem j0⟩ x ≠ 0 ∧
    (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      R.rd ⟨d.w (jj k) Z, R.w_mem (jj k)⟩ (cpt X x z) / R.rd ⟨d.w j0 Z, R.w_mem j0⟩ (cpt X x z) : V (nd X))) 0).det ≠ 0

theorem tieReading_of (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp)
    (hall : FnAlgClosed (T.Q.Xo j) T.Q.c → KappaTie j hG κ → KappaOnto h j hG κ → DTie h j hG d →
      NrmTie h j hG d κ →
      ∃ (R : ∀ Z, RdData1 d Z ((T.U j T.σ₀).X (κ Z)))
        (Gen : ∀ Z, Set (Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r))
        (pt : ∀ Z, Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r → (Om Z →+* ℂ)),
        ∀ Z, TieRd1Props h hG d κ Z (R Z) ∧ TieRd2Props d Z (R Z) (Gen Z) (pt Z) ∧ TieRd3Props d Z (R Z) ∧
          TieRd4Props d Z (R Z) (Gen Z)) :
    TieReadingSt h j hG d κ := by
  intro hF hκ hκo hd hn
  obtain ⟨R, Gen, pt, H⟩ := hall hF hκ hκo hd hn
  refine ⟨fun Z =>
    { Rg := (R Z).Rg, w_mem := (R Z).w_mem, rd := (R Z).rd, WE := (R Z).WE, wL_mem := (R Z).wL_mem,
      wt := (R Z).wt, Gen := Gen Z, Gen_sub := (H Z).2.1.1, Gen_dense := (H Z).2.1.2.1, pt := pt Z,
      pt_mem := (H Z).2.1.2.2.1, pt_onto := (H Z).2.1.2.2.2.1, w_nz := (H Z).2.2.1.2, sec := (H Z).1.1,
      inj := (H Z).1.2.1, norm := (H Z).2.1.2.2.2.2.1, ratio_rd := (H Z).2.1.2.2.2.2.2.2.2.2,
      Gen_inv := (H Z).2.1.2.2.2.2.2.1, orbit_inj := (H Z).2.1.2.2.2.2.2.2.1,
      Gen_max := (H Z).2.1.2.2.2.2.2.2.2.1, bir := (H Z).2.2.1.1, coordAt := (H Z).2.2.2 }, ?_, ?_, ?_, ?_⟩
  · intro Z u F hF
    exact (H Z).1.2.2.2.2.1 u F hF
  · intro Z u F he
    exact (H Z).1.2.2.1 u F he
  · intro Z u he
    exact (H Z).1.2.2.2.1 u he
  · intro Z u hu
    exact (H Z).1.2.2.2.2.2 u hu

end Formalism.L2.Pj
end
end

