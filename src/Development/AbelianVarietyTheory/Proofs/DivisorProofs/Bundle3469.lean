import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3449
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPreservingVectorFieldOnSmallerPreimages

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagComponentDeep
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.HSApp.geoHyp_of_parts : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif) (h : Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict) (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ Λ₀ : ℝ, WtBig P → RatGen TF.X Z Y.U P.u₁ → RatGen TF.X Z Y.U P.u₂ → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ k.beta → 1 ≤ k.abelian₂ → (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ k.abelian₂) → 1 ≤ Λ₀ → (h.data f₁ f₂ th k).ShortFamily 0 Λ₀ → (h.data f₁ f₂ th k).ShortFamily (dimFlag (T.Q.Dw j)) k.LamD → (h.data f₁ f₂ th k).ShortFamily P.T k.LamT → GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ := by
  intro hPr hGD hQ hNad hPrin hSi hFa hLie D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k Λ₀ hW hR₁ hR₂ hB hL hLe h1 hS0 hSD hST
  have hNN := hQ.nef
  have hF := hG.geo
  have hA : IsNef Y.d.c₂.F (h.geo f₁ f₂ th k).LA ∧ IsBig Y.d.c₂.F (h.geo f₁ f₂ th k).LA := by
    apply GlobalTheory.T.choice_free_section_construction <;> assumption
  obtain ⟨hnef, hbig⟩ := hA
  have hbir := GlobalTheory.HSApp.birational_of_ratGen TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k hR₁
  have hbir₂ := GlobalTheory.HSApp.geo_second_birational TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k hR₂
  obtain ⟨hms, hmb⟩ := GlobalTheory.HSApp.ready_data_mulStable_mulBound hPr D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k hB
  have hnb₂ : IsNef Y.d.c₂.F (h.data f₁ f₂ th k).L₂ ∧ IsBig Y.d.c₂.F (h.data f₁ f₂ th k).L₂ :=
    GlobalTheory.BirationalBig.isNef_and_isBig hQ _ (h.geo f₁ f₂ th k).second.toLinSys
    (h.geo f₁ f₂ th k).alg₂.variety (h.geo f₁ f₂ th k).alg₂.bpf hbir₂
  have hTC : IsTotallyComplex Y.d.c₂.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := Y.d.c₂) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  obtain ⟨hD, hT, -, -, hLam, -, hLD, hLT, -⟩ := Ready.data_numbers h f₁ f₂ th k
  refine ⟨hTC, ?_, ?_, ?_, ?_, ?_, hms, hmb, ?_, ?_, h1, hS0, ?_, ?_⟩
  · exact hbir
  · exact hnef
  · exact hbig
  · exact hnb₂.1
  · exact hnb₂.2
  · intro q σ
    rw [hLam]
    exact hLe q σ
  · rw [hLam]; exact hL
  · rw [hD, hLD]; exact hSD
  · rw [hT, hLT]; exact hST
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionGaloisFixedCanonicalNDividedFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.CanonTors

theorem galois_fixed : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (x : Over.mk (spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ jK R) ⟶ G), x ^ n = 1 → spMap σ.toAlgHom.toRingHom ≫ x.left = x.left := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hnu ζ hζ Q e hD hQ G _ _ P hC σ x hx
  obtain ⟨-, D', F, A', G', _, _, U', oA, oG, inc, pr, hG', hlin, hinc, hpr, hip, hpi, -⟩ := hC
  haveI : CharZero R := hCN.2.2.2
  have hadm : AdmBase R (maximalIdeal R) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  obtain ⟨y, hy0⟩ : ∃ y : (Over.map (jK R)).obj (TFK (R := R) (AlgebraicClosure (FractionRing R))) ⟶ G', y = x ≫ inc := ⟨_, rfl⟩
  obtain ⟨h, hh0⟩ : ∃ h : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ (Over.pullback (jK R)).obj G',
    h = (Over.mapPullbackAdj (jK R)).unit.app _ ≫ (Over.pullback (jK R)).map y := ⟨_, rfl⟩
  have hy : y ^ n = 1 := by
    rw [hy0, ← MonObj.pow_comp, hx, MonObj.one_comp]
  have hmp : ∀ m : ℕ, (Over.pullback (jK R)).map (y ^ m) = ((Over.pullback (jK R)).map y) ^ m := by
    intro m
    induction m with
    | zero => simp [Functor.map_one]
    | succ m ih => rw [pow_succ, Functor.map_mul, ih, pow_succ]
  have hh : h ^ n = 1 := by
    rw [hh0, ← MonObj.comp_pow, ← hmp, hy, Functor.map_one, MonObj.comp_one]
  haveI := U'.gen_hom
  obtain ⟨a, ha0⟩ : ∃ a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A'.A, a = h ≫ U'.gen.hom := ⟨_, rfl⟩
  have ha : a ^ n = 1 := by
    rw [ha0, ← MonObj.pow_comp, hh, MonObj.one_comp]
  have hye : y ≫ oG.act F.e = y := by
    rw [hy0, ← hpi, Category.assoc, ← Category.assoc inc, hip, Category.id_comp]
  have hae : a ≫ oA.act F.e = a := by
    rw [ha0, Category.assoc, ← hlin.ext, hh0]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hye]
  obtain ⟨f, hT, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hadm D' A' G' hG' U'
    (AlgebraicClosure (FractionRing R)) n hn
  obtain ⟨p, hp⟩ := hT.2.1 a ha
  obtain ⟨p₁, hy₁, hg₁, he₁⟩ := GlobalTheory.T.exists_equivalent_idempotent_image_fixed_torsion R hCN n hn hnu Q D' F A' G' U' oA oG hG' hlin a ha hae p ((hT.1 p a).2 hp.symm)
  have hf₁ : f p₁ = a := ((hT.2.2.1 p₁ p).2 he₁).trans hp
  obtain ⟨⟨p₁', hext⟩, hpt, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hadm D' A' G' hG' U'
    (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing R)) σ.toAlgHom n hn p₁
  obtain ⟨a', ha'⟩ := hpt a
  have h2 := (hiff p₁' a a' hext ha').1 ((hT.1 p₁ a).2 hf₁.symm)
  have heq := GlobalTheory.T.idempotent_image_nDividedPoint_galoisConj_equiv T R iw s ε n hCN hn hnu ζ hζ Q e hD hQ D' F A' G' U' oA oG hG' hlin σ p p₁ p₁' hy₁ hg₁ hext
  have haa : a' = a := ((hT.1 p₁' a').1 h2).trans (((hT.2.2.1 p₁ p₁').2 heq).symm.trans hf₁)
  rw [haa] at ha'
  have e1 : (Over.mapPullbackAdj (jK R)).homEquiv _ _ y = h := by rw [Adjunction.homEquiv_unit, hh0]
  have hyl : y.left = h.left ≫ ((Over.mapPullbackAdj (jK R)).counit.app G').left := by
    have e2 : y = (Over.map (jK R)).map h ≫ (Over.mapPullbackAdj (jK R)).counit.app G' := by
      conv_lhs => rw [← ((Over.mapPullbackAdj (jK R)).homEquiv _ _).symm_apply_apply y, e1]
      exact Adjunction.homEquiv_counit _ _ _ _
    rw [e2, Over.comp_left]
    rfl
  have hhl : spMap σ.toAlgHom.toRingHom ≫ h.left = h.left := by
    have := congrArg (· ≫ U'.gen.inv.left) ha'
    simp only [ha0, Over.comp_left, Category.assoc] at this
    rw [← Over.comp_left _ _ _ U'.gen.hom U'.gen.inv, Iso.hom_inv_id, Over.id_left, Category.comp_id] at this
    exact this.symm
  have hyx : spMap σ.toAlgHom.toRingHom ≫ y.left = y.left := by
    rw [hyl, ← Category.assoc, hhl]
  have := congrArg (· ≫ pr.left) hyx
  simp only [hy0, Over.comp_left, Category.assoc] at this
  rw [← Over.comp_left _ _ _ inc pr, hip, Over.id_left, Category.comp_id] at this
  exact this
end GlobalTheory.Mum.CanonTors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPullbackIdentificationDerivationCommutesTrans
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false
noncomputable section

open GlobalTheory.KS.DlogPol (gs_pbT gs_sub)

namespace GlobalTheory.HeatConn.Comm

theorem gs_stalkMap' {X X' Z : Scheme.{0}} (r : Z ⟶ X') (β : X' ⟶ X) (z : Z) (U : X.Opens) (h : β (r z) ∈ U)
    (a : Γ(X, U)) : (r.stalkMap z).hom (gs β (r z) U a) = gs (r ≫ β) z U a := by
  rw [← gs_pull r β z U h, gs_eq β _ U h, gs_eq r z _ h]
  exact Scheme.Hom.germ_stalkMap_apply r (β ⁻¹ᵁ U) z h _

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem cst_spMap {V V' : Type} [CommRing V] [CommRing V'] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (ψ : V' →+* V) (z : Z)
    (a : V') : cst (q ≫ spMap ψ) z a = cst q z (ψ a) := by
  rw [cst, cst, ← gs_pull _ (spMap ψ) z ⊤ trivial]
  exact congrArg (gs q z ⊤) (congrArg (fun ψ' => ψ'.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))).symm

theorem stalkMap_eq_zero {k : Type} [Field k] {A₀ B' : Scheme.{0}} (q : B' ⟶ Sp (DualNumber k)) [Flat q]
    (sc : A₀ ⟶ B') (q₀ : A₀ ⟶ Sp k) (hsc : sc ≫ q = q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (y : A₀)
    {t : B'.presheaf.stalk (sc y)} (ht : cst q (sc y) DualNumber.eps * t = 0) : (sc.stalkMap y).hom t = 0 := by
  obtain ⟨u, rfl⟩ := GlobalTheory.cst_dvd_of_cst_mul_eq_zero q (sc y) (a := DualNumber.eps) (b := DualNumber.eps)
    (fun c hc => by
      have h1 : c.fst = 0 := by simpa using congrArg TrivSqZeroExt.snd hc
      exact ⟨TrivSqZeroExt.inl c.snd, by ext <;> simp [h1]⟩) ht
  rw [map_mul, cst, gs_stalkMap' sc q y ⊤ trivial, ← cst, hsc, cst_spMap]
  have e0 : (TrivSqZeroExt.fstHom k k k).toRingHom DualNumber.eps = 0 := by simp
  rw [e0, cst, map_zero, gs_eq _ y ⊤ trivial, map_zero, map_zero, zero_mul]

end GlobalTheory.HeatConn.Comm

namespace GlobalTheory.HeatConn.Comm

theorem spMap_fst_alg (k : Type) [Field k] :
    spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
  rw [← spMap_comp]
  have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
    ext; simp
  rw [this, spMap]
  exact Spec.map_id _

theorem exists_sec {k : Type} [Field k] {S A A₀ B' : Scheme.{0}} (p : A ⟶ S) (s : Sp k ⟶ S) (q₀ : A₀ ⟶ Sp k)
    (q : B' ⟶ Sp (DualNumber k)) (m₀ : A₀ ⟶ A) (π₁ π₂ : B' ⟶ A) (pr : B' ⟶ A₀)
    (h₀ : IsPullback m₀ q₀ p s) (h₂ : IsPullback π₂ q p (spMap (algebraMap k (DualNumber k)) ≫ s))
    (h₃ : ∀ (Z : Scheme.{0}) (x : Z ⟶ B') (y : Z ⟶ Sp k),
      x ≫ q = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂)
    (hpr₁ : pr ≫ m₀ = π₂) (hpr₂ : pr ≫ q₀ = q ≫ spMap (algebraMap k (DualNumber k))) :
    ∃ sc : A₀ ⟶ B', sc ≫ pr = 𝟙 _ ∧ sc ≫ π₂ = m₀ ∧
      sc ≫ q = q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ∧ ∀ x : B', π₁ x = π₂ x := by
  have e1 := spMap_fst_alg k
  have w : m₀ ≫ p = (q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
      spMap (algebraMap k (DualNumber k)) ≫ s := by
    rw [Category.assoc, reassoc_of% e1, h₀.w]
  let sc := h₂.lift m₀ _ w
  have hs₂ : sc ≫ π₂ = m₀ := h₂.lift_fst _ _ _
  have hsq : sc ≫ q = q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := h₂.lift_snd _ _ _
  have hspr : sc ≫ pr = 𝟙 _ := h₀.hom_ext (by rw [Category.assoc, hpr₁, hs₂, Category.id_comp])
    (by rw [Category.assoc, hpr₂, reassoc_of% hsq, e1, Category.comp_id, Category.id_comp])
  have hR : IsPullback pr q q₀ (spMap (algebraMap k (DualNumber k))) :=
    IsPullback.of_right (h₁₂ := m₀) (v₁₃ := p) (h₂₂ := s) (by rw [hpr₁]; exact h₂) hpr₂ h₀
  have hL : IsPullback sc q₀ q (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) :=
    IsPullback.of_right (h₁₂ := pr) (v₁₃ := q₀) (h₂₂ := spMap (algebraMap k (DualNumber k)))
      (by rw [hspr, e1]; exact IsPullback.id_horiz q₀) hsq hR
  have surj := (GlobalTheory.EpsIso.isHomeomorph_of_isPullback hL).2.surjective
  refine ⟨sc, hspr, hs₂, hsq, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := surj x
  have := congrArg (fun g : A₀ ⟶ A => g y) (h₃ _ sc q₀ hsq)
  simpa using this

end GlobalTheory.HeatConn.Comm

namespace GlobalTheory.HeatConn.Comm

open ReciprocityTheory.ChartRestriction.G.Out.PullGtPf in
theorem const_comm {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B]
    {π : B.left ⟶ A.left} (h : IsGrpPullback B A f π) (c : 𝟙_ (Over S) ⟶ A) (c' : 𝟙_ (Over S') ⟶ B)
    (hc : c'.left ≫ π = f ≫ c.left) : (toUnit B ≫ c').left ≫ π = π ≫ (toUnit A ≫ c).left := by
  rw [Over.comp_left, Over.comp_left, toUnit_left', toUnit_left', Category.assoc, hc, ← Category.assoc,
    ← h.1.w, Category.assoc]

theorem trans_comm {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B]
    {π : B.left ⟶ A.left} (h : IsGrpPullback B A f π) (c : 𝟙_ (Over S) ⟶ A) (c' : 𝟙_ (Over S') ⟶ B)
    (hc : c'.left ≫ π = f ≫ c.left) :
    (padd B (𝟙 B) (toUnit B ≫ c')).left ≫ π = π ≫ (padd A (𝟙 A) (toUnit A ≫ c)).left := by
  let x₀ : Over.mk (B.hom ≫ f) ⟶ A := Over.homMk π h.1.w
  have e := h.2 B (𝟙 B) (toUnit B ≫ c') x₀ (toUnit _ ≫ c) (by simp [x₀]) (by
    rw [Over.comp_left, Over.comp_left, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.toUnit_left',
      ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.toUnit_left', Category.assoc, hc]
    rfl)
  have e2 : x₀ * (toUnit _ ≫ c) = x₀ ≫ (𝟙 A * (toUnit A ≫ c)) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  change (𝟙 B * (toUnit B ≫ c')).left ≫ π = π ≫ (𝟙 A * (toUnit A ≫ c)).left
  rw [← e, e2]
  rfl

theorem exists_lift {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {k : Type} [Field k]
    (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left)
    (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)) (h₁ : IsGrpPullback B' Q.P.A (spMap ρ) π₁)
    (h₂ : IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂)
    (hc : ∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧
      c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left) (α : Q.X) (j : Fin 4) :
    ∃ φ' : B'.left ⟶ B'.left, φ' ≫ B'.hom = B'.hom ∧ φ' ≫ π₁ = π₁ ≫ Q.famφB α j ∧ φ' ≫ π₂ = π₂ ≫ Q.famφB α j := by
  have hcB : ∀ y, c' y ≫ B'.hom = (𝟙_ (Over (Sp (DualNumber k)))).hom := fun y => (hc y).1
  let cB : Q.X → (𝟙_ (Over (Sp (DualNumber k))) ⟶ B') := fun y => Over.homMk (c' y) (hcB y)
  have h1 : ∀ y, (cB y).left ≫ π₁ = spMap ρ ≫ (Q.c y).left := fun y => (hc y).2.1
  have h2 : ∀ y, (cB y).left ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left := fun y => (hc y).2.2
  fin_cases j
  · exact ⟨𝟙 _, Category.id_comp _, (Category.id_comp _).trans (Category.comp_id _).symm,
      (Category.id_comp _).trans (Category.comp_id _).symm⟩
  · exact ⟨(padd B' (𝟙 B') (toUnit B' ≫ cB α)).left, Over.w _, trans_comm h₁ _ _ (h1 α),
      trans_comm h₂ _ _ (h2 α)⟩
  · exact ⟨(toUnit B' ≫ cB α).left, Over.w _, const_comm h₁ _ _ (h1 α), const_comm h₂ _ _ (h2 α)⟩
  · exact ⟨(toUnit B' ≫ η[B']).left, Over.w _,
      const_comm h₁ _ _ (ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h₁),
      const_comm h₂ _ _ (ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h₂)⟩

end GlobalTheory.HeatConn.Comm

namespace GlobalTheory.HeatConn.Comm

theorem commutes : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {k : Type} [Field k] (ρ : R →+* DualNumber k) (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsGrpPullback A₀ Q.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left) → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → (∀ (W : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → Commutes Q m₀ ed := by
  intro R _ _ Q k _ ρ A₀ _ m₀ hA₀ ed B' _ π₁ π₂ c' h₁ h₂ h₃ hc pr hpr₁ hpr₂ hD α j T hT₁ hT₂ W f Z b z hz
  have hfA : Flat Q.P.A.hom := by
    have := Q.P.smoothDim
    have : Smooth Q.P.A.hom := SmoothOfRelativeDimension.smooth Q.P.g _
    infer_instance
  have hfB : Flat B'.hom := MorphismProperty.of_isPullback h₁.1 hfA
  obtain ⟨φ', hφ'0, hφ'1, hφ'2⟩ := exists_lift Q ρ B' π₁ π₂ c' h₁ h₂ hc α j
  have e2 : spMap (constHom ρ) = spMap (algebraMap k (DualNumber k)) ≫
      spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := spMap_comp _ _
  obtain ⟨sc, hspr, hs₂, hsq, hpts⟩ := exists_sec Q.P.A.hom _ A₀.hom B'.hom m₀ π₁ π₂ pr hA₀.1
    (e2 ▸ h₂.1) h₃ hpr₁ hpr₂
  have hpre : ∀ U : Q.P.A.left.Opens, π₂ ⁻¹ᵁ U ≤ π₁ ⁻¹ᵁ U := fun U x hx => by
    change π₁ x ∈ U
    rw [hpts x]
    exact hx
  have hprle : ∀ U : Q.P.A.left.Opens, π₂ ⁻¹ᵁ U ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ U) := fun U x hx => by
    change m₀ (pr x) ∈ U
    have : (pr ≫ m₀) x ∈ U := by rw [hpr₁]; exact hx
    simpa using this
  have hφpr : φ' ≫ pr = pr ≫ T := hA₀.1.hom_ext
    (by rw [Category.assoc, Category.assoc, hpr₁, hφ'2, hT₁, ← Category.assoc, hpr₁])
    (by rw [Category.assoc, Category.assoc, hpr₂, ← Category.assoc, hφ'0, hT₂, hpr₂])
  set φ := Q.famφB α j with hφdef
  have key : ∀ y : A₀.left, (T ≫ m₀) y ∈ W →
      gs (𝟙 _) y (m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W)) (ed _ ((φ.app W).hom f)) = gs T y (m₀ ⁻¹ᵁ W) (ed W f) := by
    intro y hy
    have hy' : φ (m₀ y) ∈ W := by
      have h := hy
      rw [hT₁] at h
      all_goals simpa using h
    have m₂ : sc y ∈ π₂ ⁻¹ᵁ (φ ⁻¹ᵁ W) := by
      change φ (π₂ (sc y)) ∈ W
      have : (sc ≫ π₂) y = m₀ y := by rw [hs₂]
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact hy'
    have m₃ : φ' (sc y) ∈ π₂ ⁻¹ᵁ W := by
      change π₂ (φ' (sc y)) ∈ W
      have : (φ' ≫ π₂) (sc y) = φ (π₂ (sc y)) := by rw [hφ'2]; simp
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact m₂
    have eA := congrArg (gs (𝟙 B'.left) (sc y) (π₂ ⁻¹ᵁ (φ ⁻¹ᵁ W))) (hD (φ ⁻¹ᵁ W) ((φ.app W).hom f))
    rw [gs_add (𝟙 _) (sc y) _ m₂, gs_mul (𝟙 _) (sc y) _ m₂, gs_pbT (𝟙 _) π₁ (sc y) (hpre _) m₂,
      gs_pbT (𝟙 _) π₂ (sc y) le_rfl m₂, gs_pbT (𝟙 _) pr (sc y) (hprle _) m₂, gs_constFn B'.hom _ (𝟙 _) (sc y) m₂] at eA
    have eB := congrArg (gs φ' (sc y) (π₂ ⁻¹ᵁ W)) (hD W f)
    rw [gs_add φ' (sc y) _ m₃, gs_mul φ' (sc y) _ m₃, gs_pbT φ' π₁ (sc y) (hpre _) m₃,
      gs_pbT φ' π₂ (sc y) le_rfl m₃, gs_pbT φ' pr (sc y) (hprle _) m₃, gs_constFn B'.hom _ φ' (sc y) m₃, hφ'1, hφ'2, hφ'0, hφpr] at eB
    simp only [Category.id_comp] at eA
    have m₁' : φ (π₁ (sc y)) ∈ W := by rw [hpts]; exact m₂
    rw [← gs_pull π₁ φ (sc y) W m₁', ← gs_pull π₂ φ (sc y) W m₂] at eB
    have hk : cst B'.hom (sc y) DualNumber.eps * (gs pr (sc y) (m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W)) (ed _ ((φ.app W).hom f)) -
        gs (pr ≫ T) (sc y) (m₀ ⁻¹ᵁ W) (ed W f)) = 0 := by
      linear_combination eB - eA
    have h0 := stalkMap_eq_zero B'.hom sc A₀.hom hsq y hk
    have hy0 : pr (sc y) = y := by
      have := congrArg (fun g : A₀.left ⟶ A₀.left => g y) hspr
      simpa using this
    have ma : pr (sc y) ∈ m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W) := by
      change φ (m₀ (pr (sc y))) ∈ W
      rw [hy0]; exact hy'
    have mb : (pr ≫ T) (sc y) ∈ m₀ ⁻¹ᵁ W := by
      change m₀ ((pr ≫ T) (sc y)) ∈ W
      simp only [Scheme.Hom.comp_apply]
      rw [hy0]; simpa using hy
    rw [map_sub, gs_stalkMap' sc pr y _ ma, gs_stalkMap' sc (pr ≫ T) y _ mb, hspr, reassoc_of% hspr] at h0
    exact sub_eq_zero.1 h0
  have hyz : (T ≫ m₀) (b z) ∈ W := by simpa using hz
  have mz1 : b z ∈ m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W) := by
    change φ (m₀ (b z)) ∈ W
    have h := hyz
    rw [hT₁] at h
    all_goals simpa using h
  have mz2 : T (b z) ∈ m₀ ⁻¹ᵁ W := by
    change m₀ (T (b z)) ∈ W
    simpa using hyz
  rw [gs_stalkMap b z _ mz1, key (b z) hyz, gs_stalkMap' b T z _ mz2]

end GlobalTheory.HeatConn.Comm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPullbackIsomorphismUnitConstantPlusEpsFunctioStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_pullback_isomorphism_unit_constant_plus_eps_function : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ P.L.U (jj i)) → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → ∃ (a : kˣ) (b : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) (algebraMap k (DualNumber k) (a : k)) + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (b i) (π₂ ⁻¹ᵁ V i) := by
  first | exact @GlobalTheory.UnitPart.unitPart | exact GlobalTheory.UnitPart.unitPart | (intros; apply GlobalTheory.UnitPart.unitPart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointFromFormalRaynaudPointSameDerivaStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_point_from_formal_raynaud_point_same_derivations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∀ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ), GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f) := by
  first | exact @GlobalTheory.Heat.FormalDer.main | exact GlobalTheory.Heat.FormalDer.main | (intros; apply GlobalTheory.Heat.FormalDer.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryApproxPoincareSeriesAtMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem uApproxAt_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (φ : InvFun (𝓞 E)) (d m : ℕ), 1 ≤ m → UApproxAt X₁ φ d → UApproxAt X₁ φ (d * m) := by
  intro E _ _ _ H Dw l Xo c C X₁ φ d m hm hd p _ z₁ t₀ e
  obtain ⟨f, hf0, hf⟩ := hd p z₁ t₀ e
  have hpow : ∀ t : UCTrait X₁ p z₁, ‖t.val (f ^ m)‖ = ‖t.val f‖ ^ m := fun t => by
    rw [UModel.val_eq_valInt, UModel.val_eq_valInt, map_pow]
    push_cast
    exact norm_pow _ _
  have hexp : ∀ t : UCTrait X₁ p z₁, Real.exp (-(t.sc * (((d * m : ℕ) : ℝ) * φ.evalZ t.T.be))) =
      Real.exp (-(t.sc * (d * φ.evalZ t.T.be))) ^ m := fun t => by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨f ^ m, ?_, fun t => ?_⟩
  · rw [hpow, hf0, hexp]
  · rcases hf t with h1 | ⟨h, hh, h2⟩
    · left
      rw [hpow, hexp]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 m
    · right
      refine ⟨h, hh, ?_⟩
      rw [hpow]
      exact (pow_le_of_le_one (norm_nonneg _) (UModel.norm_val_le t f) (by omega)).trans h2

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPreservingVectorFieldOnSmallerPreimagesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_preserving_vectorField_on_smaller_preimages : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (d : Fld Y.H.left), IsField (Y.q.left ⁻¹ᵁ V.1) d → (∀ (α : Q.X) f, IsWt Y α (Y.q.left ⁻¹ᵁ V.1) f → IsWt Y α _ (d _ f)) → ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  first | exact @GlobalTheory.Heat.WtSub.isWt_field_of_le | exact GlobalTheory.Heat.WtSub.isWt_field_of_le | (intros; apply GlobalTheory.Heat.WtSub.isWt_field_of_le <;> assumption)
end

