import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGroupRightActionComponents
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompAct

open ReciprocityTheory.ChartRestriction.G.FD

theorem exists_action {H G C : Type} [Group H] [Group G] (comp : H → C) (hs : ∀ x, ∃ h, comp h = x)
    (Lift : G → H → Prop) (hex : ∀ g, ∃ k, Lift g k) (h1 : Lift 1 1)
    (hmul : ∀ g g' k k', Lift g k → Lift g' k' → Lift (g * g') (k * k'))
    (key : ∀ g k k' h h', Lift g k → Lift g k' → comp h = comp h' → comp (h * k) = comp (h' * k')) :
    ∃ mv : C → G → C, (∀ x, mv x 1 = x) ∧ (∀ x g g', mv x (g * g') = mv (mv x g) g') ∧ (∀ x, ∃ h, comp h = x) ∧
      ∀ g k, Lift g k → ∀ h, comp (h * k) = mv (comp h) g := by
  choose rep hrep using hs
  choose l hl using hex
  have main : ∀ g k, Lift g k → ∀ h, comp (h * k) = comp (rep (comp h) * l g) :=
    fun g k hk h => key g k (l g) h _ hk (hl g) (hrep _).symm
  refine ⟨fun x g => comp (rep x * l g), fun x => ?_, fun x g g' => ?_, fun x => ⟨rep x, hrep x⟩, main⟩
  · have := main 1 1 h1 (rep x)
    rw [mul_one, hrep] at this
    exact this.symm
  · show comp (rep x * l (g * g')) = comp (rep (comp (rep x * l g)) * l g')
    rw [← main g' (l g') (hl g'), mul_assoc]
    exact key (g * g') _ _ _ _ (hl _) (hmul _ _ _ _ (hl g) (hl g')) rfl

theorem frame_calc {n : Type} [Fintype n] [DecidableEq n] (x B P Q P' M : Matrix n n ℂ) (hy : (B * x).det ≠ 0)
    (h1 : M * B = B * Q) (h2 : P * Q = P') : P * x * ((B * x)⁻¹ * M * (B * x)) = P' * x := by
  have hx : IsUnit x.det := by
    rw [Matrix.det_mul] at hy
    exact (right_ne_zero_of_mul hy).isUnit
  have e : M * (B * x) = (B * x) * (x⁻¹ * (Q * x)) := by
    rw [← Matrix.mul_assoc M, h1, Matrix.mul_assoc B x, Matrix.mul_nonsing_inv_cancel_left _ _ hx, Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ M, e, Matrix.nonsing_inv_mul_cancel_left _ _ hy.isUnit, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ hx, ← Matrix.mul_assoc, h2]

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem archM_mul (V : HSp D) (hr : V.rank = r) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g g' : GA D V) :
    Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ g) * Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ g') =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (g * g')) := by
  have e : archM V θ (g * g') = archM V θ g * archM V θ g' := by
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  rw [e]
  exact Matrix.submatrix_mul_equiv _ _ _ (finCongr hr).symm _

theorem coset_of_comp_eq {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hf : ∀ h, ∃ p : GA D V, ∀ τ : (X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) p) * x₀ τ.1)
    {h h' : GA D V} (e : (dict h).1 = (dict h').1) :
    ∃ a ∈ GinfC V, ∃ γ ∈ GQ V, ∃ k ∈ Kf, h * a = γ * h' * k := by
  obtain ⟨-, -, ⟨x0, h0, h3⟩, -, -, h6⟩ := hd
  have hf' : ∀ g c x, dict g = ⟨c, x⟩ → ∃ p : GA D V, ∀ τ : (X c).Ψ, mat x τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th c τ) p) * x₀ τ.1 := by
    intro g c x hg
    have := hf g
    rw [hg] at this
    exact this
  have h6' : ∀ g g' c x, dict g = ⟨c, x⟩ → (∃ γ' ∈ (X c).Γ, dict g' = ⟨c, lact γ' x⟩) →
      ∃ γ ∈ GQ V, ∃ k ∈ Kf, g' = γ * g * k := by
    intro g g' c x hg hh
    refine h6 g g' ?_
    rw [hg]
    exact hh
  obtain ⟨x', hx'⟩ : ∃ x' : Frame (X (dict h).1).Ψ r, dict h' = ⟨(dict h).1, x'⟩ := by
    generalize (dict h).1 = c at e
    subst e
    exact ⟨_, rfl⟩
  obtain ⟨hdom, g0, hg0⟩ := h0 (dict h).1
  obtain ⟨b, hb⟩ := hf' _ _ _ hg0
  obtain ⟨p, hp⟩ := hf h
  obtain ⟨p', hp'⟩ := hf' _ _ _ hx'
  obtain ⟨a, a1, a2⟩ := GlobalTheory.UnitarySplit.ga_glue V _ 1 (GlobalTheory.UnitarySplit.infHom_mem V (b * (p⁻¹ * p') * b⁻¹)) (one_mem _)
  obtain ⟨γ', hγ', he⟩ := h3 h a a2
  refine ⟨a, a2, h6' h' _ _ x' hx' ⟨γ', hγ', he.trans ?_⟩⟩
  congr 2
  funext τ
  have ha : archM V (th (dict h).1 τ) a = archM V (th (dict h).1 τ) (b * (p⁻¹ * p') * b⁻¹) := by
    unfold archM
    rw [a1]
  show (mat (dict h).2 τ * ((mat (x0 (dict h).1) τ)⁻¹ * Matrix.reindex (finCongr hr) (finCongr hr)
    (archM V (th (dict h).1 τ) a) * mat (x0 (dict h).1) τ) : Matrix (Fin r) (Fin r) ℂ) = mat x' τ
  have hy := (hdom τ).1
  rw [hb τ] at hy
  rw [hp τ, hp' τ, hb τ, ha]
  refine frame_calc _ _ _ (Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) (p⁻¹ * p'))) _ _ hy ?_ ?_
  · rw [archM_mul, archM_mul, inv_mul_cancel_right]
  · rw [archM_mul, mul_inv_cancel_left]

theorem comm_real_fin (V : HSp D) {a k : GA D V} (ha : a ∈ GinfC V) (hk : k ∈ GfC V) : a * k = k * a := by
  refine GlobalTheory.UnitarySplit.ga_ext V ?_ ?_
  · rw [map_mul, map_mul, show infHom V k = 1 from hk, mul_one, one_mul]
  · rw [map_mul, map_mul, show finHom V a = 1 from ha, mul_one, one_mul]

theorem exists_action_dict {V W : HSp D} (hV : V = W) {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hf : ∀ h, ∃ p : GA D V, ∀ τ : (X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) p) * x₀ τ.1)
    (β : GL (Fin W.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ W.rank) {G : Type} [Group G] (eG : G →* G0 L.Pg L.r)
    (hK : ∀ k : GA D W, Lev.IsLevelLift W β L 1 k ↔ cast (congrArg (GA D) hV.symm) k ∈ Kf)
    (hex : ∀ g, ∃ k, Lev.IsLevelLift W β L (eG g) k) :
    ∃ mv : Comp → G → Comp, (∀ x, mv x 1 = x) ∧ (∀ x g g', mv x (g * g') = mv (mv x g) g') ∧
      (∀ x, ∃ h, (castDict hV dict h).1 = x) ∧ ∀ g k, Lev.IsLevelLift W β L (eG g) k →
        ∀ h, (castDict hV dict (h * k)).1 = mv (castDict hV dict h).1 g := by
  subst hV
  have hK' : ∀ k : GA D V, Lev.IsLevelLift V β L 1 k ↔ k ∈ Kf := hK
  refine exists_action (fun h => (dict h).1) (fun x => ?_) (fun g k => Lev.IsLevelLift V β L (eG g) k) hex ?_ ?_ ?_
  · obtain ⟨x0, h0, -⟩ := hd.2.2.1
    obtain ⟨g, hg⟩ := (h0 x).2
    exact ⟨g, congrArg Sigma.fst hg⟩
  · show Lev.IsLevelLift V β L (eG 1) 1
    rw [map_one]
    exact (hK' 1).2 (one_mem _)
  · intro g g' k k' hk hk'
    show Lev.IsLevelLift V β L (eG (g * g')) (k * k')
    rw [map_mul]
    exact GlobalTheory.ProjComm.isLift_mul hk hk'
  · intro g k k' h h' hk hk' e
    obtain ⟨a, ha, γ, hγ, k0, hk0, he⟩ := coset_of_comp_eq hd x₀ hf e
    have h1 := GlobalTheory.ProjComm.isLift_mul (GlobalTheory.ProjComm.isLift_mul (GlobalTheory.ProjComm.isLift_inv hk') ((hK' k0).2 hk0)) hk
    rw [mul_one, inv_mul_cancel] at h1
    have h2 : h * k * a = γ * (h' * k' * (k'⁻¹ * k0 * k)) := by
      rw [mul_assoc h, ← comm_real_fin V ha hk.1, ← mul_assoc h, he]
      group
    obtain ⟨x0, -, h3⟩ := hd.2.2.1
    obtain ⟨_, -, e1⟩ := h3 (h * k) a ha
    obtain ⟨_, -, e2⟩ := hd.1 γ hγ (h' * k' * (k'⁻¹ * k0 * k))
    obtain ⟨_, -, e3⟩ := hd.2.1 _ ((hK' _).1 h1) (h' * k')
    have f1 := congrArg Sigma.fst e1
    have f2 := congrArg Sigma.fst e2
    have f3 := congrArg Sigma.fst e3
    rw [h2] at f1
    exact f1.symm.trans (f2.trans f3)

set_option maxHeartbeats 1000000 in

theorem exists_action_components : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → ∃ mv : (T.U ((i : ℕ) + 1) σ).Comp → G → (T.U ((i : ℕ) + 1) σ).Comp, (∀ x, mv x 1 = x) ∧ (∀ x g g', mv x (g * g') = mv (mv x g) g') ∧ (∀ x, ∃ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 = x) ∧ ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 = mv (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 g := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hR ht hpb i σ hσ hV hex
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨th, hr, hth, hd⟩ := ht.laws.dictU _ hj σ hσ
  obtain ⟨hr', g, e, F, ik, φ, th', -, -, hth', -, hL⟩ := ht.laws.adPin _ hj σ hσ
  have e' : th' = th := funext fun k => funext fun τ => GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (hth' k τ) (hth k τ)
  subst e'
  exact exists_action_dict hV hd (T.x₀ _ σ) (fun h => (hL h).elim fun γ hγ => ⟨γ * h, hγ.2.2.2⟩)
    (R.βW i) (R.datWp i R.triv) R.eG.toMonoidHom (GlobalTheory.T.level_character_embedding_compat T R κ v₀ hR ht hpb i σ hσ hV) hex

end GlobalTheory.CompAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameOfProjective
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self)

namespace GlobalTheory.VB.Summand

theorem free_of_free_away {R M R' M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing R'] [Algebra R R'] [AddCommGroup M'] [Module R M'] [Module R' M']
    [IsScalarTower R R' M'] (r : R) [IsLocalization.Away r R'] (f : M →ₗ[R] M')
    [IsLocalizedModule (.powers r) f]
    [Module.Free (Localization (.powers r)) (LocalizedModule.Away r M)] : Module.Free R' M' := by
  set e := (IsLocalization.algEquiv (.powers r) (Localization (.powers r)) R').toRingEquiv
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.of_ringEquiv_symm e
  refine Module.Free.of_equiv (σ := (e : Localization (.powers r) →+* R'))
    { __ := IsLocalizedModule.iso (.powers r) f, map_smul' := ?_ }
  intro a x
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers r) a
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
  simp [e, ← map_smul, ← smul_assoc]

variable {X : Scheme.{0}} {F G : X.Modules} {U : X.Opens}

theorem isFrame_of_affine_basis [G.IsQuasicoherent] (hU : IsAffineOpen U) {ι : Type} [Fintype ι]
    (b : Module.Basis ι Γ(X, U) Γ(G, U)) : IsFrame (F := G) (U := U) b := by
  refine isFrame_of_forall_exists fun V h x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := QCoh.exists_affine_mem_le x hx
  refine ⟨W, hle, hxW, ?_⟩
  letI := QCoh.resAlgebra (hle.trans h)
  letI := QCoh.resModule G (hle.trans h)
  haveI := QCoh.res_isScalarTower G (hle.trans h)
  let b' := (QCoh.isBaseChange_resLinear G hU hW (hle.trans h)).basis b
  have hb (i : ι) : b' i = resM G (hle.trans h) (b i) := by
    rw [IsBaseChange.basis_apply]
    rfl
  have : Fintype.linearCombination Γ(X, W) (fun i => resM G (hle.trans h) (b i)) =
      b'.equivFun.symm.toLinearMap := by
    ext a : 1
    simp [Fintype.linearCombination_apply, hb]
  rw [this]
  exact b'.equivFun.symm.bijective

theorem exists_frame_of_projective [G.IsQuasicoherent] (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) Γ(G, U)] [Module.Projective Γ(X, U) Γ(G, U)] (y : U) :
    ∃ (V : X.Opens) (n : ℕ) (e : Fin n → Γ(G, V)), (y : X) ∈ V ∧ IsFrame e := by
  have := Module.finitePresentation_of_projective Γ(X, U) Γ(G, U)
  have := hU.isLocalization_stalk y
  have := QCoh.isLocalizedModule_germLinear G hU y
  have hbc := QCoh.isBaseChange_germLinear G hU y
  have : Module.Finite (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :) :=
    .equiv hbc.equiv
  have : Module.Projective (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :) :=
    .of_equiv hbc.equiv
  have : Module.Free (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (hU.primeIdealOf y).asIdeal.primeCompl (QCoh.germLinear G y) (X.presheaf.stalk (y : X))
  have hxf := (QCoh.mem_primeCompl_primeIdealOf_iff hU y f).1 hf
  have := hU.isLocalization_basicOpen f
  have := QCoh.isLocalizedModule_resBasicOpen G hU f
  have : Module.Free Γ(X, X.basicOpen f) Γ(G, X.basicOpen f) :=
    free_of_free_away f (QCoh.resBasicOpen G f)
  have : Module.Finite Γ(X, X.basicOpen f) Γ(G, X.basicOpen f) :=
    Module.Finite.of_isLocalizedModule (.powers f) (QCoh.resBasicOpen G f)
  exact ⟨_, _, _, hxf, (isFrame_of_affine_basis (hU.basicOpen f)
    (Module.Free.chooseBasis _ _)).comp_equiv (Fintype.equivFin _).symm⟩

end GlobalTheory.VB.Summand

theorem GlobalTheory.VB.isVB_of_retract : ∀ (X : Scheme.{0}) [IsIntegral X] (F G : X.Modules) (i : G ⟶ F)
    (q : F ⟶ G) (r : ℕ), i ≫ q = 𝟙 G → IsVB F r → IsVB G (genRank G) := by
  intro X _ F G i q r hiq hF x
  have := hF.isQuasicoherent
  have hs : ∑ _ : Unit, i ≫ q = 𝟙 G := by simpa using hiq
  have : G.IsQuasicoherent :=
    QCoh.isQuasicoherent_of_sum_eq_id (A := fun _ : Unit => F) (fun _ => i) (fun _ => q) hs
  obtain ⟨U, e, hU, hx, -, he⟩ := hF.exists_affine (V := ⊤) (x := x) trivial
  have := Module.Free.of_basis (he.basis le_rfl)
  have := Module.Finite.of_basis (he.basis le_rfl)
  have hc : QCoh.appLinear q U ∘ₗ QCoh.appLinear i U = LinearMap.id := LinearMap.ext fun s => by
    simpa using QCoh.sum_app_app (A := fun _ : Unit => F) (fun _ => i) (fun _ => q) hs s
  have : Module.Projective Γ(X, U) Γ(G, U) := .of_split _ _ hc
  have : Module.Finite Γ(X, U) Γ(G, U) :=
    .of_surjective (QCoh.appLinear q U) fun s => ⟨_, LinearMap.congr_fun hc s⟩
  obtain ⟨V, n, e', hxV, he'⟩ := Summand.exists_frame_of_projective (G := G) hU ⟨x, hx⟩
  have hn : genRank G = n :=
    (Module.finrank_eq_card_basis (he'.stalkBasis _ (genericPoint_mem hxV))).trans
      (Fintype.card_fin n)
  subst hn
  exact ⟨V, e', hxV, he'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeLatticeGermSystem
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AwayOrb.Cpt
open scoped RestrictedProduct
variable {p : ℕ} [Fact p.Prime]

theorem eventually_int_of_isCompact (K : Set (AfP p)) (hK : IsCompact K) :
    ∀ᶠ w in Filter.cofinite, ∀ x ∈ K, AfP.eval w x ∈ w.1.adicCompletionIntegers ℚ := by
  let U : Finset (AwayP p) → Set (AfP p) := fun F =>
    {f : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ] |
      ∀ i, i ∉ F → f.1 i ∈ (i.1.adicCompletionIntegers ℚ : Set (i.1.adicCompletion ℚ))}
  have hU : ∀ F, IsOpen (U F) := fun F =>
    RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _) (p := fun i => i ∉ F)
  have hcov : K ⊆ ⋃ F, U F := by
    intro x _
    have hx := x.2
    rw [Filter.eventually_cofinite] at hx
    refine Set.mem_iUnion.2 ⟨hx.toFinset, fun i hi => ?_⟩
    by_contra h
    exact hi (hx.mem_toFinset.2 h)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcov
  let S : Finset (AwayP p) := t.biUnion id
  rw [Filter.eventually_cofinite]
  refine S.finite_toSet.subset fun w hw => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hw
  obtain ⟨x, hxK, hxw⟩ := hw
  obtain ⟨F, hF, hxF⟩ := Set.mem_iUnion₂.1 (ht hxK)
  by_contra hwS
  exact hxw (hxF w fun hwF => hwS (Finset.mem_biUnion.2 ⟨F, hF, hwF⟩))

theorem repr_map_eval (G : HTGroup p) (w : AwayP p) (x : AfP p ⊗[ℚ] G.C) (i : Fin (Module.finrank ℚ G.C)) :
    (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) (Module.finBasis ℚ G.C)).repr
        (Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) x) i =
      AfP.eval w ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r c =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]

theorem continuous_coord (G : HTGroup p) (i : Fin (Module.finrank ℚ G.C)) :
    Continuous fun x : G.GAf => (Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
      (((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  exact (IsModuleTopology.continuous_of_linearMap
    ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).coord i)).comp
    (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val))

theorem continuous_coord_inv (G : HTGroup p) (i : Fin (Module.finrank ℚ G.C)) :
    Continuous fun x : G.GAf => (Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
      ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) i := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) (AfP p ⊗[ℚ] G.C)
  exact (IsModuleTopology.continuous_of_linearMap
    ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).coord i)).comp
    (Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val))

theorem continuous_sim (G : HTGroup p) :
    Continuous fun x : G.GAf => (((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)

theorem continuous_sim_inv (G : HTGroup p) :
    Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)

theorem eventually_mem_intPts (G : HTGroup p) (Ω : Set G.GAf) (hΩ : IsCompact Ω) :
    ∀ᶠ w in Filter.cofinite, ∀ h ∈ Ω, compL G w h ∈ intPts G w := by
  have h1 : ∀ᶠ w in Filter.cofinite, ∀ i, ∀ h ∈ Ω, AfP.eval w
      ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
        (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i =>
      (eventually_int_of_isCompact _ (hΩ.image (continuous_coord G i))).mono fun w hw h hh =>
        hw _ (Set.mem_image_of_mem _ hh)
  have h2 : ∀ᶠ w in Filter.cofinite, ∀ i, ∀ h ∈ Ω, AfP.eval w
      ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
        ((((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) i) ∈
        w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i =>
      (eventually_int_of_isCompact _ (hΩ.image (continuous_coord_inv G i))).mono fun w hw h hh =>
        hw _ (Set.mem_image_of_mem _ hh)
  have h3 := eventually_int_of_isCompact _ (hΩ.image (continuous_sim G))
  have h4 := eventually_int_of_isCompact _ (hΩ.image (continuous_sim_inv G))
  filter_upwards [h1, h2, h3, h4] with w hw1 hw2 hw3 hw4 h hh
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
  · have e := repr_map_eval G w (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i
    have := hw1 i h hh
    rw [← e] at this
    exact this
  · have e := repr_map_eval G w ((((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) :
      AfP p ⊗[ℚ] G.C) i
    have := hw2 i h hh
    rw [← e] at this
    exact this
  · exact hw3 _ (Set.mem_image_of_mem _ hh)
  · exact hw4 _ (Set.mem_image_of_mem _ hh)

end GlobalTheory.AwayOrb.Cpt

theorem GlobalTheory.AwayOrb.eventually_compL_mem_intPts : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf),
    IsCompact Ω → ∀ᶠ w in Filter.cofinite, ∀ h ∈ Ω, compL G w h ∈ intPts G w :=
  fun _ _ G Ω hΩ => GlobalTheory.AwayOrb.Cpt.eventually_mem_intPts G Ω hΩ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseDifferentMaxValuationStatement
section
open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverseDifferent_max_valuation : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ e : E, e ≠ 0 ∧ (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) ∧ ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) → w.valuation E f ≤ w.valuation E e := by
  first | exact @GlobalTheory.invDifferent_exists_max_valuation | exact GlobalTheory.invDifferent_exists_max_valuation | (intros; apply GlobalTheory.invDifferent_exists_max_valuation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPlaceDatumOverNumberFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_place_datum_over_number_field : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_vP → ∀ (i : Fin D.R.m), VStd D i → ∀ (t : T0) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ M' : IntermediateField ℚ ℂ, M ≤ M' → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ J : Ideal (𝓞 D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) → ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M', PhiIs R i M'.val.toRingHom t ι (J • ⊤) φ := by
  first | exact @GlobalTheory.LevelDatum.exists_phi | exact GlobalTheory.LevelDatum.exists_phi | (intros; apply GlobalTheory.LevelDatum.exists_phi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalBasisAtPrimeOfIsLatticeStatement
section
open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localBasis_at_prime_of_isLattice : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E → ∃ X : Matrix (Fin n) (Fin n) E, IsUnit X.det ∧ (∀ j, (fun i => X i j) ∈ L) ∧ ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1 := by
  first | exact @GlobalTheory.exists_local_basis_of_isLattice | exact GlobalTheory.exists_local_basis_of_isLattice | (intros; apply GlobalTheory.exists_local_basis_of_isLattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixAdjoinTensorUnramifiedOfCommuteSeparStatement
section
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrixAdjoinTensorUnramified_of_commute_separable : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (γ : Matrix (Fin n) (Fin n) K), 0 < r → γ.charpoly.Separable → ∀ X : Matrix (Fin n) (Fin n) (KQ p K r), Commute X (γ.map (inclK p K r)) → ∃ x, GlobalTheory.PolyTensor.phi p K n γ r x = X := by
  first | (exact @GlobalTheory.PolyTensorCommutant.exists_phi_eq) | (exact GlobalTheory.PolyTensorCommutant.exists_phi_eq) | (intros; apply GlobalTheory.PolyTensorCommutant.exists_phi_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulVeryAmpleSubIsEffectivePicClass
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

theorem exists_nsmul_sub_eff : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [Nonempty Y] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hH : H.IsLB) (hM : M.IsLB), GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ c : ℕ, GlobalTheory.EffBound.Eff (c • GlobalTheory.CechPic.cls H hH - GlobalTheory.CechPic.cls M hM) := by
  intro R _ Y f _ H m s M hH hM hs
  have hD : (dual M).IsLB := isLB_dual hM
  obtain ⟨t₀, ht⟩ := exists_sec_tw_ne_zero R Y f H m s (dual M) hH hD hs
  refine ⟨(max t₀ 0).toNat, ?_⟩
  have hc : t₀ ≤ ((max t₀ 0).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (le_max_right _ _)]; exact le_max_left _ _
  obtain ⟨σ, i, hσ⟩ := ht _ hc
  have key := eff_of_sec _ (isLB_tw hD hH _) σ i hσ
  have e : cls (tw (dual M) H ((max t₀ 0).toNat : ℤ)) (isLB_tw hD hH _) =
      cls (dual M) hD - cls (pw H (-((max t₀ 0).toNat : ℤ))) (isLB_pw hH _) :=
    cls_div hD (isLB_pw hH _) (isLB_tw hD hH _)
  rw [e, cls_pw hH, cls_dual hM hD, neg_zsmul, natCast_zsmul] at key
  convert key using 1
  abel
end GlobalTheory.EffBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefMajorantOfPositiveIndexOneStatement
section
open Matrix GlobalTheory.LKTrip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_posDef_majorant_of_positiveIndex_one : ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), H.det ≠ 0 → sigPosH hH = 1 → ∀ z : Fin n → ℂ, 0 < (star z ⬝ᵥ H *ᵥ z).re → ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧ ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c : ℂ), 0 < s → Yᴴ * H * Y = (s : ℂ) • H → Y *ᵥ z = c • z → Yᴴ * P * Y = (s : ℂ) • P := by
  first | (exact @GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one) | (exact GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one) | (intros; apply GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeEqSpanOfCoheightLeOneStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' : ∀ (R : Type) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (X : Scheme.{0}) (q : X ⟶ Sp R), GeneralizingMap q → ∀ x : X, Order.coheight x ≤ 1 → (q x).asIdeal ≠ ⊥ → ∃ π : R, Prime π ∧ (q x).asIdeal = Ideal.span {π} := by
  first | exact @GlobalTheory.exists_prime_eq_span_of_coheight_le_one | exact GlobalTheory.exists_prime_eq_span_of_coheight_le_one | (intros; apply GlobalTheory.exists_prime_eq_span_of_coheight_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulRatEqIntOfIntegralAwayStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_mul_rat_eq_int_of_integral_away : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), (∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) → ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z := by
  first | (exact @GlobalTheory.ratint_away) | (exact GlobalTheory.ratint_away) | (intros; apply GlobalTheory.ratint_away  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPointPolynomialIdempotentUnitValueStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalPoint_polynomial_idempotentUnit_value : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F))) (ψ : Polynomial (AE F E)), (∀ (Ω : Type) [Field Ω] (φ : AE F E →+* Ω), φ (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) * ψ.eval (algebraMap F (AE F E) t) + (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S))) := by
  first | exact @GlobalTheory.DenseAvoid.exists_unit_eval | exact GlobalTheory.DenseAvoid.exists_unit_eval | (intros; apply GlobalTheory.DenseAvoid.exists_unit_eval <;> assumption)
end

