import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0029
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.SecPtRed
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section Ev

variable (Xr : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
  {K2 : Type} [Field K2] (ev : Rp Xr la N →+* K2) (hu : IsUnit (ev (sec Xr la w 0)))

lemma liftEv_alg (r : Rp Xr la N) :
    IsLocalization.Away.lift (sec Xr la w 0) hu (algebraMap (Rp Xr la N) (Lw Xr la w) r) = ev r :=
  IsLocalization.lift_eq _ r

lemma liftEv_w0inv :
    IsLocalization.Away.lift (sec Xr la w 0) hu (w0inv Xr la w) = (ev (sec Xr la w 0))⁻¹ := by
  have := congrArg (IsLocalization.Away.lift (sec Xr la w 0) hu) (section_mul_inverse_eq_one Xr la w)
  rw [map_mul, liftEv_alg, map_one] at this
  exact eq_inv_of_mul_eq_one_right this

lemma liftEv_frac (k : ℕ) (g : Rp Xr la N) :
    IsLocalization.Away.lift (sec Xr la w 0) hu (frac Xr la w k g) = ev g * (ev (sec Xr la w 0))⁻¹ ^ k := by
  rw [frac_apply, map_mul, map_pow, liftEv_alg, liftEv_w0inv]

end Ev

section Std

variable {Xr : PJ D B P j} {la : HeightOneSpectrum (𝓞 B.KO)} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData Xr ka wL wF}

theorem isUnif_of_ring (hfd : FiniteDimensional (Kp Xr la G.N) (OsK Xr la G.w)) :
    IsUnif (OsK Xr la G.w) (unifO Xr la G.N) := by
  have : Algebra.IsIntegral (Kp Xr la G.N) (OsK Xr la G.w) := Algebra.IsIntegral.of_finite _ _
  exact isUnif_of_field (Kp Xr la G.N)
    (Op.irreducible_map Xr la G.N (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (Xr.Ol la))))

theorem kp_charZero' : CharZero (Kp Xr la G.N) := by
  have := Kl_charZero Xr la
  exact charZero_of_injective_algebraMap (algebraMap (Xr.Kl la) (Kp Xr la G.N)).injective

theorem isDVRAt_of_ring (hfd : FiniteDimensional (Kp Xr la G.N) (OsK Xr la G.w)) (hred : IsReduced (OsK Xr la G.w))
    (ζ : PtsG G la) : IsDVRAt ζ := by
  have := kp_charZero' (la := la) (G := G)
  exact (integralClosure_dvr' (Op Xr la G.N) (Kp Xr la G.N) (OsK Xr la G.w)).2 ζ

theorem loc_charZero (h : IsUnif (OsK Xr la G.w) (unifO Xr la G.N)) (ζ : PtsG G la) [IsDVRAt ζ] :
    CharZero (Loc ζ) := by
  have hK := kp_charZero' (la := la) (G := G)
  have hO : CharZero (Op Xr la G.N) :=
    (RingHom.charZero_iff (IsFractionRing.injective (Op Xr la G.N) (Kp Xr la G.N))).2 hK
  refine charZero_of_injective_algebraMap (R := Op Xr la G.N) ?_
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 h.irreducible
  rw [map_mul, map_pow] at ha
  have hb : algebraMap (Op Xr la G.N) (Loc ζ) (unifO Xr la G.N) ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (Op Xr la G.N) ↥(As (Op Xr la G.N) (OsK Xr la G.w)) (Loc ζ)]
    intro h0
    exact vL_ne_top ζ (unif_mem_nonZeroDivisors h) ((vL_eq_top_iff ζ _).2 h0)
  exact (mul_ne_zero ((u.isUnit.map (algebraMap (Op Xr la G.N) (Loc ζ))).ne_zero) (pow_ne_zero n hb)) ha

end Std

variable {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

theorem addVal_map_of_unr {W V : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (ι : W →+* V) (hunr : ∃ ϖ : W, Irreducible ϖ ∧ Irreducible (ι ϖ)) (r : W) :
    IsDiscreteValuationRing.addVal V (ι r) = IsDiscreteValuationRing.addVal W r := by
  obtain ⟨ϖ, hϖ, hιϖ⟩ := hunr
  by_cases hr : r = 0
  · subst hr
    rw [map_zero, IsDiscreteValuationRing.addVal_zero, IsDiscreteValuationRing.addVal_zero]
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n, map_mul, map_pow]
  exact IsDiscreteValuationRing.addVal_def' ((u.isUnit.map ι).unit) hιϖ n

theorem fromW_of {ζ : PtsG G la} [IsDVRAt ζ] {y : E.Pt' la}
    (h : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N))
    (T : CDVR) (ι : Loc ζ →+* T.V) (hloc : IsLocalHom ι) (hunr : ∃ ϖ : Loc ζ, Irreducible ϖ ∧ Irreducible (ι ϖ))
    (ev : Rp (xplus X E hM) la G.N →+* T.Fr) (hu : IsUnit (ev (sec (xplus X E hM) la G.w 0)))
    (hv : ∀ (w : WeightFamilies.Wt D j) (F : B.Cusp j w), E.vAt' la y (X.inc w F) =
      nval T.V (ep (unifO (xplus X E hM) la G.N) ζ) (ev (emb (xplus X E hM) la G.N (X.inc w F))))
    (hdeg : ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
      IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w) =
        phiAt ζ T.Fr ι h (addVal_map_of_unr ι hunr) (toOsK (xplus X E hM) la G.w x)) :
    Nonempty (FromW ζ y) := by
  have hι : AddValPres ζ ι := addVal_map_of_unr ι hunr
  have honS : ∀ i : Fin (WeightFamilies.dimY D j), ev (sec (xplus X E hM) la G.w i.succ) = 0 := by
    intro i
    have h1 := hdeg (sfr (xplus X E hM) la G.w i.succ)
    rw [(toOsK_eq_zero_iff _ _ _ _).2 (sfr_succ_mem_Jid _ _ _ i), map_zero, coe_sfr, liftEv_frac] at h1
    exact (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ (inv_ne_zero hu.ne_zero))
  have hord : ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
      toE (ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w x)) =
        nval T.V 1 (IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w)) := by
    intro x
    rw [hdeg x]
    exact toE_ord_eq T.Fr h hι _
  let sp : SecPt ζ y :=
    { T := T, ep_pos := ep_pos ζ h, ev := ev, hv := hv, onS := honS, s0 := hu, ord := hord }
  have hevW : ∀ (x : ↥(Frac0 (xplus X E hM) la G.w))
      (a : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))),
      toOsK (xplus X E hM) la G.w x = (a : OsK (xplus X E hM) la G.w) →
      IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w) =
        algebraMap T.V T.Fr (ι (algebraMap _ (Loc ζ) a)) := by
    intro x a hxa
    rw [hdeg x, hxa]
    exact phiAt_coe T.Fr h hι a
  exact ⟨{ toSecPt := sp
           ι := ι
           loc := hloc
           unr := hunr
           evW := hevW }⟩

theorem secPtSt_of
    (hR : ∀ ζ : PtsG G la, ∃ y : E.Pt' la, Nonempty (FromW ζ y)) :
    SecPtSt G la :=
  fun ζ => (hR ζ).imp fun _ ⟨f⟩ => ⟨f.toSecPt⟩

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.UnifGen
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem scal_mul {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem gen_unit {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} (s s' : LB.Sec (PPx x))
    (hs : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s.f i)
    (hs' : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s'.f i) :
    ∃ u : Sˣ, ∀ i, s'.f i = scal x (u : S) i * s.f i := by
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨b, hb, -⟩ := hs' s
  obtain ⟨c1, -, hc1⟩ := hs s
  have h1 : b * a = 1 := by
    have e1 : ∀ i, s.f i = scal x (b * a) i * s.f i := fun i => by
      rw [scal_mul, mul_assoc, ← ha i, ← hb i]
    have e2 : ∀ i, s.f i = scal x 1 i * s.f i := fun i => by rw [scal_one, one_mul]
    exact (hc1 _ e1).trans (hc1 _ e2).symm
  exact ⟨⟨a, b, by rw [mul_comm]; exact h1, h1⟩, ha⟩

theorem frBor_of_tri {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (hx : y'.x = y.x)
    (hu : ∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → S, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
      IsCombAt y.x (y.u τ) cf (y'.u τ i)) :
    ∃ t : Ix Dw → Sˣ, FrBor t y y' := by
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  simp only at hx hu
  subst hx
  obtain ⟨u0, hu0⟩ := gen_unit (x := y.x) y.s s' y.gen gen'
  classical
  refine ⟨fun o => match o with
    | none => u0
    | some p => (hu p.1 p.2).choose_spec.1.unit, rfl, fun τ i => ?_, 𝟙 _, ?_, ?_, ?_⟩
  · exact ⟨(hu τ i).choose, (hu τ i).choose_spec.1.unit_spec.symm, (hu τ i).choose_spec.2.1,
      (hu τ i).choose_spec.2.2⟩
  · exact Category.id_comp _
  · exact Category.id_comp _
  · intro i h
    simp only
    rw [← hu0 i]
    simp only [Scheme.Hom.appLE]
    have e : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
    rw [e]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl

theorem frBor_trans (hT : TanLin Xo) {S : Type} [CommRing S] [Algebra c.F S] {y y' y'' : FrPt Xo c S}
    {t1 t2 : Ix Dw → Sˣ} (h1 : FrBor t1 y y') (h2 : FrBor t2 y' y'') : ∃ t : Ix Dw → Sˣ, FrBor t y y'' := by
  obtain ⟨hx1, hu1, -⟩ := h1
  obtain ⟨hx2, hu2, -⟩ := h2
  refine frBor_of_tri y y'' (hx2.trans hx1) fun τ i => ?_
  choose cf1 h1a h1b h1c using hu1 τ
  obtain ⟨cf2, h2a, h2b, h2c⟩ := hu2 τ i
  let A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S := Matrix.of fun k j => cf1 j k
  have h2c' : IsCombAt y.x (y'.u τ) cf2 (y''.u τ i) := by rw [← hx1]; exact h2c
  have hc := hT S y.x (y.u τ) (y.tan τ) (y'.u τ) A cf2 (y''.u τ i) (fun j => h1c j) h2c'
  refine ⟨A.mulVec cf2, ?_, fun k hk => ?_, hc⟩
  · have e : A.mulVec cf2 i = cf1 i i * cf2 i := by
      simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply]
      refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · rw [h1b j i hlt, zero_mul]
      · rw [h2b j hgt, mul_zero]
    rw [e, h1a i, h2a]
    exact (Units.isUnit _).mul (Units.isUnit _)
  · simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases le_or_gt j i with hji | hij
    · rw [h1b j k (lt_of_le_of_lt hji hk), zero_mul]
    · rw [h2b j hij, mul_zero]

end Gen

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.XcLat
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} (T : Core D)

namespace Core

abbrev C (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule T.Q.c.F (T.R j) := T.cuspA j (wtA w) w.n

abbrev Vs (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Set (T.R j → EReal) :=
  valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la

def Ns (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : T.R j → ℝ :=
  supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n

def Cu (j : ℕ) : Type := {_cu : FJ.CuF (T.X₀ j) (WeightFamilies.rho D j) // InR D j}

def Xc (j : ℕ) (cu : T.Cu j) : Submodule (𝓞 D.host.E) (Fin (WeightFamilies.rho D j) → D.host.E) :=
  FJ.XcF (T.X₀ j) T.frI cu.1

theorem Xc_lat (j : ℕ) (cu : T.Cu j) : Submodule.IsLattice D.host.E (T.Xc j cu) :=
  FJ.xcLatF (T.X₀ j) T.frI one_ne_zero cu.1

abbrev FJt (j : ℕ) (cu : T.Cu j) (_χ : WeightFamilies.ExpoSet D (T.Xc j cu)) (_w : WeightFamilies.Wt D j) : Type :=
  FJ.FJtF T.σ₀ (T.X₀ j) cu.1

end Core

variable {T} (h : LawsCore T)

namespace LawsCore

open Classical in

def Nl (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : T.R j → ℝ :=
  if hj : InR D j then
    l2C (T.U j) (goodOf T.Q.c σ) (T.V j _) (T.dict j _) (T.mu j _) (xiR D) (wtA w) w.n
      (h.cuspidalL2Subspace j hj _ (goodEmb_goodOf _ σ) _ _ (dom_wtA w))
  else 0

def sg (j : ℕ) (cu : T.Cu j) (χ : WeightFamilies.ExpoSet D (T.Xc j cu)) (w : WeightFamilies.Wt D j) :
    T.C j w →ₗ[T.Q.c.F] T.FJt j cu χ w :=
  FJ.sgF T.σ₀ (T.X₀ j) (rdC (T.U j) T.σ₀ (wtA w) w.n)
    (FJ.rdOrbInt_of_latZ T.σ₀ (T.X₀ j) _ (rdC_continuousOn (h.unf j cu.2 T.σ₀ T.good_σ₀) (dom_wtA w)) (h.latZ j cu.2))
    cu.1 χ.1

include h

theorem fd (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) : FiniteDimensional T.Q.c.F (T.C j w) := by
  exact h.cuspFD j hj (wtA w) w.n (dom_wtA w)

theorem hNs (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : IsNormOn (T.C j w) σ (T.Ns j w σ) :=
  (isNormOn_supC _ (h.supDef j hj) (dom_wtA w) (goodEmb_goodOf _ σ)).of_goodOf

theorem hNl (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : IsNormOn (T.C j w) σ (h.Nl j w σ) := by
  rw [Nl, dif_pos hj]
  exact (isNormOn_l2C _ (h.l2Def j hj _ (goodEmb_goodOf _ σ)) (dom_wtA w)).of_goodOf

theorem hle (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) :
    ∀ f ∈ T.C j w, h.Nl j w σ f ≤ T.Ns j w σ f := by
  rw [Nl, dif_pos hj]
  obtain ⟨_, _, _, hD⟩ := h.dictU j hj _ (goodEmb_goodOf _ σ)
  exact l2C_le_supC _ (goodEmb_goodOf _ σ) _ hD.2.2.2.1 (h.muUnit j hj _ (goodEmb_goodOf _ σ))

theorem mul (j : ℕ) (hj : InR D j) (w w' : WeightFamilies.Wt D j) :
    ∀ f ∈ T.C j w, ∀ g ∈ T.C j w', f * g ∈ T.C j (WeightAlgebra.wadd w w') := by
  intro f hf g hg
  have e := h.cuspMul j hj (wtA w) (wtA w') w.n w'.n f g (dom_wtA w) (dom_wtA w') hf hg
  have e1 : f * g = mulC (T.Q.Xo j) T.Q.c f g := rfl
  have e2 : (WeightAlgebra.wadd w w').n = w.n + w'.n := rfl
  have e3 : wtA (WeightAlgebra.wadd w w') = wtA w + wtA w' := by
    clear e e1 e2 hf hg f g h
    funext x
    simp only [wtA, WeightAlgebra.wadd, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have e4 : ∀ {p : ℕ} (a b : Fin p → ℕ) k, ext0 (fun i => a i + b i) k = ext0 a k + ext0 b k := by
      intro p a b k
      unfold ext0
      split_ifs <;> simp
    simp only [e4]
    split_ifs <;> omega
  show f * g ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA (WeightAlgebra.wadd w w')) (WeightAlgebra.wadd w w').n
  rw [e1, e2, e3]
  exact e

end LawsCore

abbrev recB : WeightFamilies.Prov D :=
  mkB T.Q.eO T.C h.fd T.Vs (fun _ la => isVal_valSet la) T.Ns h.Nl h.hNs h.hNl h.hle T.Cu T.Xc T.Xc_lat T.FJt h.sg

end Formalism.L2.Pj
end
end

