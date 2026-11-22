import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0005
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0833
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorEqOfTangentDerivativeAtOriginEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiIsEven
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPointOfWeightNumerical
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.RefSum

theorem len_mul_total_le {T F m q N B Sg b l x C₁ C₂ K U : ℝ} (hT : 1 ≤ T) (hF : 1 ≤ F) (hm : 1 ≤ m) (hq : q ≤ m)
    (hB : 0 ≤ B) (hb : 1 ≤ b) (hl : 1 ≤ l) (hx : 1 ≤ x) (h1 : 0 ≤ C₁) (h2 : 0 ≤ C₂) (hK : 0 ≤ K)
    (a1 : T * (B + 1) ≤ C₁ * b) (a2 : T * Sg ≤ C₁ * b) (a3 : T * N ^ 3 ≤ C₂ * b) (a4 : F * m * b * l * x ≤ C₂ * U) :
    T * (40 * ((F * m * (B + 1) + F * (Sg + 2 * q * B)) * (K * l) * (K * x) + F * N ^ 3 * (K * l) + (2 * B + 1))) ≤
      40 * (4 * C₁ * K ^ 2 + C₂ * K + 2 * C₁) * C₂ * U := by
  have hcb : 0 ≤ C₁ * b := by positivity
  have b1 : T * B ≤ C₁ * b := by nlinarith
  have b2 : q * (T * B) ≤ m * (C₁ * b) := mul_le_mul hq b1 (by positivity) (by positivity)
  have b3 : m * (T * (B + 1)) ≤ m * (C₁ * b) := mul_le_mul_of_nonneg_left a1 (by positivity)
  have b4 : C₁ * b ≤ m * (C₁ * b) := le_mul_of_one_le_left hcb hm
  have b5 : T * (m * (B + 1) + (Sg + 2 * q * B)) ≤ 4 * (m * (C₁ * b)) := by nlinarith
  have c1 : T * (m * (B + 1) + (Sg + 2 * q * B)) * (F * (K * l) * (K * x)) ≤
      4 * (m * (C₁ * b)) * (F * (K * l) * (K * x)) := mul_le_mul_of_nonneg_right b5 (by positivity)
  have hmx : 1 ≤ m * x := one_le_mul_of_one_le_of_one_le hm hx
  have c2 : T * N ^ 3 * (F * (K * l)) ≤ C₂ * b * (F * (K * l)) := mul_le_mul_of_nonneg_right a3 (by positivity)
  have c3 : C₂ * b * (F * (K * l)) ≤ C₂ * b * (F * (K * l)) * (m * x) := le_mul_of_one_le_right (by positivity) hmx
  have hall : 1 ≤ F * l * (m * x) := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hF hl) hmx
  have c4 : C₁ * b ≤ C₁ * b * (F * l * (m * x)) := le_mul_of_one_le_right hcb hall
  have c5 : T * (2 * B + 1) ≤ 2 * (C₁ * b) := by nlinarith
  have c6 : (4 * C₁ * K ^ 2 + C₂ * K + 2 * C₁) * (F * m * b * l * x) ≤ (4 * C₁ * K ^ 2 + C₂ * K + 2 * C₁) * (C₂ * U) :=
    mul_le_mul_of_nonneg_left a4 (by positivity)
  nlinarith

theorem log_top_le {T B b l C₁ C₂ : ℝ} (hT : 1 ≤ T) (hB : 0 ≤ B) (hb : 1 ≤ b) (hl : 1 ≤ l) (h1 : 0 ≤ C₁)
    (a1 : T * (B + 1) ≤ C₁ * b) (a2 : Real.log b ≤ C₂ * l) : Real.log (2 * B + 1) ≤ (2 * C₁ + C₂ + 1) * l := by
  have b1 : B + 1 ≤ C₁ * b := by nlinarith
  have b2 : Real.log (2 * B + 1) ≤ Real.log ((2 * C₁ + 1) * b) := Real.log_le_log (by positivity) (by nlinarith)
  rw [Real.log_mul (by positivity) (by positivity)] at b2
  have b3 : Real.log (2 * C₁ + 1) ≤ 2 * C₁ + 1 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  nlinarith

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem sumAt_of_sizes {PP C₁ C₂ : ℝ} (h1 : 0 ≤ C₁) (h2 : 0 ≤ C₂) (u1 : Weight (dat p i))
    (hw : WtAt p i PP C₁ u1) (hn : NumAt p i PP C₂) :
    GlobalTheory.RefSum.SumAt p i PP
      (40 * (4 * C₁ * (2 * C₁ + C₂ + 1) ^ 2 + C₂ * (2 * C₁ + C₂ + 1) + 2 * C₁) * C₂) u1 := by
  obtain ⟨hs, hk, B, Sg, hwt, a1, a2, hT1⟩ := hw
  obtain ⟨hl, hb, n1, hx, n2, n3, n4, n5, n6, n7⟩ := hn
  have hT1' : (1 : ℝ) ≤ lenT p i PP := by exact_mod_cast hT1
  have hexp := GlobalTheory.T.thetaExponents_bigSmallFactorBounds _ _ (dat p i) D.R.f D.R.k D.R.m (nCol (dat p i)) B Sg u1 hs hk hwt
  have hd : p.T.Q.H.d = D.host.d := p.fw.laws.pins.1.1
  have htwo := GlobalTheory.CharDepth.twoPlaces_host D p.T.Q.H hd
  have hvd : ∀ q, 0 ≤ D.host.vdH q := D.host.vdH_nonneg
  obtain ⟨hsum, h2S, hunr⟩ := UpperTheory.KR.small_vd_sum D.host.toHostAx
  have hN : (dat p i).p + (dat p i).q = D.R.r := by
    have := hs.1
    unfold Ranks.r
    omega
  have hF : (1 : ℝ) ≤ D.R.f := by
    have hn : 0 < D.R.n := D.R.ord_pos
    exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast hs.2.2.2.1
  have hq : ((dat p i).q : ℝ) ≤ D.R.m := by exact_mod_cast hs.2.1
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  set K : ℝ := 2 * C₁ + C₂ + 1 with hK
  have hK1 : 1 ≤ K := by linarith
  have hK2 : C₂ ≤ K := by linarith
  have hKl : C₂ * L.sc.L ≤ K * L.sc.L := mul_le_mul_of_nonneg_right hK2 (by linarith)
  have hnum := GlobalTheory.T.weightedPrimeLogSum_oscillationBound_le D.R.f D.R.r D.R.k D.R.m (2 * B + 1) (B + 1) (D.R.f * (Sg + 2 * (dat p i).q * B))
    D.host.vdH (K * L.sc.L) (K * Real.log (Real.log L.sc.x)) D.host.small {D.host.q, D.host.d} hexp.1
    ((Nat.cast_nonneg _).trans hexp.2.2.1) hvd (hN ▸ hs.1) hs.2.2.1 hs.2.2.2.1
    (one_le_mul_of_one_le_of_one_le hK1 hl) (one_le_mul_of_one_le_of_one_le hK1 hx)
    (by push_cast; exact log_top_le hT1' hB hb hl h1 a1 n1) (n4.trans hKl)
    (hsum.trans (mul_le_mul_of_nonneg_left (n5.trans hKl) (by norm_num)))
    (n3.trans (mul_le_mul_of_nonneg_right hK2 (by linarith))) Finset.card_le_two
    (fun q hq => (n7 q hq).trans (by nlinarith))
  refine ⟨_, _, _, hnum, ?_, fun q hqp _ => ?_⟩
  · push_cast
    exact len_mul_total_le hT1' hF hm hq hB hb hl hx h1 h2 (by linarith) a1 a2 n6 n2
  · have := GlobalTheory.T.depthOscillation_le_bound_every_prime _ _ (dat p i) _ (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c D.R.f D.R.k D.R.m (2 * B + 1) (B + 1) _ _ hs hexp
      D.host.vdH D.host.small {D.host.q, D.host.d} hvd (fun r _ hr => (htwo r hr).2.1) h2S (by simp [hd])
      (fun r hr hr2 hrR => hunr r hr hr2
        (fun h => hrR (by simp [h])) (fun h => hrR (by simp [h]))) q
    rw [hN] at this
    simpa only [if_pos hqp.out] using this

end Point

theorem sumPt_of_sizes : WtPt → NumPt → SumPt := fun hw hn =>
  Closed.imp (Closed.and hw hn) fun _ _ _ ⟨⟨C₁, h1, e1⟩, C₂, h2, e2⟩ =>
    ⟨40 * (4 * C₁ * (2 * C₁ + C₂ + 1) ^ 2 + C₂ * (2 * C₁ + C₂ + 1) + 2 * C₁) * C₂, by positivity,
      (e1.and e2).imp fun _ h x hx hle ι p hp i hi u1 hu =>
        sumAt_of_sizes p i h1 h2 u1 ((h x hx hle ι p hp).1 i hi u1 hu) ((h x hx hle ι p hp).2 i hi)⟩

end GlobalTheory.RefSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_over_lift_of_range_subset {T : Scheme.{0}} {Z H V : Over T} (e : V ⟶ H) [IsOpenImmersion e.left]
    (f : Z ⟶ H) (h : Set.range f.left ⊆ Set.range e.left) : ∃ a : Z ⟶ V, a ≫ e = f := by
  refine ⟨Over.homMk (IsOpenImmersion.lift e.left f.left h) ?_, ?_⟩
  · rw [← Over.w e, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w f]
  · ext
    simp

theorem surjective_mul_of_open_of_irreducible_fibres : ∀ (T : Scheme.{0}) (H V : Over T) [GrpObj H] (e : V ⟶ H), IsOpenImmersion e.left → Surjective V.hom → (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ T), IrreducibleSpace (pullback H.hom t : Scheme.{0})) → Surjective ((fst V V ≫ e) * (snd V V ≫ e)).left := by
  intro T H V _ e he hV hirr
  refine ⟨fun x => ?_⟩
  let t : Spec (CommRingCat.of (H.left.residueField x)) ⟶ T := H.left.fromSpecResidueField x ≫ H.hom
  let g : Over.mk t ⟶ H := Over.homMk (H.left.fromSpecResidueField x) rfl
  have hI := hirr (H.left.residueField x) t
  let X : Over T := Over.mk (pullback.snd H.hom t ≫ t)
  let p : X ⟶ H := Over.homMk (pullback.fst H.hom t) pullback.condition
  let c : X ⟶ Over.mk t := Over.homMk (pullback.snd H.hom t) rfl
  let φ : X ⟶ H := (c ≫ g) * p⁻¹
  let Y : Over T := Over.mk (pullback.snd V.hom t ≫ t)
  let q : Y ⟶ V := Over.homMk (pullback.fst V.hom t) pullback.condition
  let d : Y ⟶ Over.mk t := Over.homMk (pullback.snd V.hom t) rfl
  have hl : ∀ h : Y ⟶ H, ∃ l : Y ⟶ X, l ≫ p = h ∧ l ≫ c = d := by
    intro h
    refine ⟨Over.homMk (pullback.lift h.left (pullback.snd V.hom t) (Over.w h)) ?_, ?_, ?_⟩
    · exact pullback.lift_snd_assoc _ _ _ _
    · ext; exact pullback.lift_fst _ _ _
    · ext; exact pullback.lift_snd _ _ _
  have hY : Nonempty Y.left := by
    have : Surjective (pullback.snd V.hom t) := inferInstance
    obtain ⟨y, -⟩ := (pullback.snd V.hom t).surjective (closedPoint _)
    exact ⟨y⟩
  obtain ⟨y⟩ := hY
  have hopen : IsOpen (Set.range e.left) := e.left.isOpenEmbedding.isOpen_range
  have hne : ∀ (l : Y ⟶ X) (ψ : X ⟶ H), l ≫ ψ = q ≫ e → (ψ.left ⁻¹' Set.range e.left).Nonempty := by
    intro l ψ h
    refine ⟨l.left y, q.left y, ?_⟩
    change (q ≫ e).left y = (l ≫ ψ).left y
    rw [h]
  have h1 : (p.left ⁻¹' Set.range e.left).Nonempty := by
    obtain ⟨l, hlp, -⟩ := hl (q ≫ e)
    exact hne l p hlp
  have h2 : (φ.left ⁻¹' Set.range e.left).Nonempty := by
    obtain ⟨l, hlp, hlc⟩ := hl ((q ≫ e)⁻¹ * (d ≫ g))
    refine hne l φ ?_
    simp only [φ]
    rw [MonObj.comp_mul, GrpObj.comp_inv, hlp, ← Category.assoc, hlc]
    group
  have hI' : IrreducibleSpace X.left := hI
  have ho1 : IsOpen (p.left ⁻¹' Set.range e.left) := hopen.preimage p.left.continuous
  have ho2 : IsOpen (φ.left ⁻¹' Set.range e.left) := hopen.preimage φ.left.continuous
  obtain ⟨z, hz1, hz2⟩ := nonempty_preirreducible_inter ho1 ho2 h1 h2
  let U : X.left.Opens := ⟨_, ho1.inter ho2⟩
  let Z : Over T := Over.mk (U.ι ≫ X.hom)
  let j : Z ⟶ X := Over.homMk U.ι rfl
  obtain ⟨a, ha⟩ := exists_over_lift_of_range_subset e (j ≫ φ) (by
    rintro _ ⟨u, rfl⟩
    exact u.2.2)
  obtain ⟨b, hb⟩ := exists_over_lift_of_range_subset e (j ≫ p) (by
    rintro _ ⟨u, rfl⟩
    exact u.2.1)
  have key : lift a b ≫ ((fst V V ≫ e) * (snd V V ≫ e)) = j ≫ c ≫ g := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, ha, hb, ← MonObj.comp_mul]
    simp only [φ, inv_mul_cancel_right]
  let u : Z.left := (⟨z, hz1, hz2⟩ : U)
  refine ⟨(lift a b).left u, ?_⟩
  change (lift a b ≫ ((fst V V ≫ e) * (snd V V ≫ e))).left u = x
  rw [key]
  exact H.left.fromSpecResidueField_apply x _

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFiniteCommGroupSchemeCoboundaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.CharKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricTwoCocycle_finiteCommGroupScheme_coboundary : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : Over (Sp K)) [GrpObj N] [IsCommMonObj N], IsFinite N.hom → ∀ c : Γ((N ⊗ N).left, ⊤)ˣ, (∀ (T : Over (Sp K)) (x y z : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (lift (x * y) z).left c = GlobalTheory.CharKer.pullTop (lift y z).left c * GlobalTheory.CharKer.pullTop (lift x (y * z)).left c) → (∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c = GlobalTheory.CharKer.pullTop (lift y x).left c) → ∃ u : Γ(N.left, ⊤)ˣ, ∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (x * y).left u = GlobalTheory.CharKer.pullTop x.left u * GlobalTheory.CharKer.pullTop y.left u := by
  first | exact @GlobalTheory.SymCob.exists_coboundary | exact GlobalTheory.SymCob.exists_coboundary | (intros; apply GlobalTheory.SymCob.exists_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeAtOriginAddTangentVectorStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentDerivativeAtOrigin_add_tangentVector : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (u v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)), tanDer G (u + v) f = tanDer G u f + tanDer G v f := by
  first | exact @GlobalTheory.CoordsOrigin.tanDer_add | exact GlobalTheory.CoordsOrigin.tanDer_add | (intros; apply GlobalTheory.CoordsOrigin.tanDer_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeAtOriginSmulTangentVectorStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentDerivativeAtOrigin_smul_tangentVector : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (r : R) (v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)), tanDer G (r • v) f = r * tanDer G v f := by
  first | exact @GlobalTheory.CoordsOrigin.tanDer_smul | exact GlobalTheory.CoordsOrigin.tanDer_smul | (intros; apply GlobalTheory.CoordsOrigin.tanDer_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackChainCompat
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TangentBaseChange

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_tangent_baseChange : ∀ (R₀ R : Subring ℂ) (ic : R₀ →+* R), (∀ x, ((ic x : R) : ℂ) = x) →
  ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp ℂ)) [GrpObj A]
    (g : G.left ⟶ G₀.left) (p : A.left ⟶ G.left), IsGrpPullback G G₀ (spMap ic) g → IsGrpPullback A G (spMap R.subtype) p →
    ∀ (v₀ : epsR R₀ ⟶ G₀) (v' : epsR ℂ ⟶ A), IsTangent v₀ →
      v'.left ≫ p ≫ g = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left →
      ∃ v : epsR R ⟶ G, IsTangent v ∧ v'.left ≫ p = spMap (Chart.dualMapR R.subtype) ≫ v.left := by
  intro R₀ R ic hic G₀ _ G _ A _ g p hg hp v₀ v' hv₀ hv'
  have hw : (spMap (Chart.dualMapR ic) ≫ v₀.left) ≫ G₀.hom =
      spMap (algebraMap R (DualNumber R)) ≫ spMap ic := by
    rw [Category.assoc, Over.w v₀]
    show spMap (Chart.dualMapR ic) ≫ spMap (algebraMap R₀ (DualNumber R₀)) = _
    rw [spMap_comp_ring, spMap_comp_ring]
    congr 1
    ext x
    · simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let vl : (epsR R).left ⟶ G.left := hg.1.lift _ _ hw
  have hvg : vl ≫ g = spMap (Chart.dualMapR ic) ≫ v₀.left := hg.1.lift_fst _ _ hw
  have hvG : vl ≫ G.hom = spMap (algebraMap R (DualNumber R)) := hg.1.lift_snd _ _ hw
  refine ⟨Over.homMk vl hvG, ?_, ?_⟩
  · show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ vl = η[G].left
    apply hg.1.hom_ext
    · have e : η[G].left ≫ g = spMap ic ≫ η[G₀].left := GlobalTheory.PolBaseChange.eSec_comm hg
      have t : spMap (TrivSqZeroExt.fstHom R₀ R₀ R₀).toRingHom ≫ v₀.left = η[G₀].left := hv₀
      have hr : ((TrivSqZeroExt.fstHom R R R).toRingHom).comp (Chart.dualMapR ic) =
          ic.comp (TrivSqZeroExt.fstHom R₀ R₀ R₀).toRingHom := by
        refine RingHom.ext fun x => ?_
        simp [Chart.dualMapR]
      rw [Category.assoc, hvg, ← Category.assoc, spMap_comp_ring, hr, ← spMap_comp_ring,
        Category.assoc, t, e]
    · have hr : ((TrivSqZeroExt.fstHom R R R).toRingHom).comp (algebraMap R (DualNumber R)) =
          RingHom.id R := by
        refine RingHom.ext fun x => ?_
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [Category.assoc, hvG, spMap_comp_ring, hr, Over.w η[G]]
      simp
  · apply hg.1.hom_ext
    · have hr : (Chart.dualMapR R.subtype).comp (Chart.dualMapR ic) = Chart.dualMapR R₀.subtype := by
        refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
        · simp [Chart.dualMapR, hic]
        · simp [Chart.dualMapR, hic]
      show (v'.left ≫ p) ≫ g = (spMap (Chart.dualMapR R.subtype) ≫ vl) ≫ g
      rw [Category.assoc, hv', Category.assoc, hvg, ← Category.assoc, spMap_comp_ring, hr]
    · show (v'.left ≫ p) ≫ G.hom = (spMap (Chart.dualMapR R.subtype) ≫ vl) ≫ G.hom
      rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w v', Category.assoc, hvG]
      show spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap R.subtype =
        spMap (Chart.dualMapR R.subtype) ≫ spMap (algebraMap R (DualNumber R))
      rw [spMap_comp_ring, spMap_comp_ring]
      congr 1
      ext x
      · simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
      · simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.TangentBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackEllipticModelStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_pullback_elliptic_model : ∀ (R : Type) [CommRing R] (σ : R →+* ℂ) (P : Out.PolAV (Sp R)) (A' : Over (Sp ℂ)) [GrpObj A']
    (φ' : A'.left ⟶ P.A.left) (L' : LB A'.left) (u : HolUnif A' L' 1) (v : epsR R ⟶ P.A) (v' : epsR ℂ ⟶ A') (t : ℂ)
    (S : Set ℂ), IsAbelianScheme A' → SmoothOfRelativeDimension 1 A'.hom → IsGrpPullback A' P.A (spMap σ) φ' →
    (∀ w, w ∈ u.Λ ↔ w 0 ∈ S) → IsTangent v → IsTangent v' → v'.left ≫ φ' = spMap (Chart.dualMapR σ) ≫ v.left →
    u.IsDiff (fun _ ↦ t) v' → ∀ (g : ℕ) (j₀ : Fin g),
    ∃ (P₀ : Out.PolAV (Sp R)) (A₀ : Over (Sp ℂ)) (_ : GrpObj A₀) (φ₀ : A₀.left ⟶ P₀.A.left) (L₀ : LB A₀.left)
      (u₀ : HolUnif A₀ L₀ g) (v₀ : epsR R ⟶ P₀.A) (v₀' : epsR ℂ ⟶ A₀),
      IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension g A₀.hom ∧ IsGrpPullback A₀ P₀.A (spMap σ) φ₀ ∧
      (∀ w, w ∈ u₀.Λ ↔ ∀ j, w j ∈ S) ∧ IsTangent v₀ ∧ IsTangent v₀' ∧
      v₀'.left ≫ φ₀ = spMap (Chart.dualMapR σ) ≫ v₀.left ∧ u₀.IsDiff (Pi.single j₀ t) v₀' := by
  first | exact @GlobalTheory.PowFibre.exists_pow | exact GlobalTheory.PowFibre.exists_pow | (intros; apply GlobalTheory.PowFibre.exists_pow <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackPrimitiveCrystallineClassEpsPartI
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

theorem snd_epsHom {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (z : DualNumber D) : (epsHom φ z).snd = φ z.snd := by
  simp [epsHom, DualNumber.lift_apply_apply]

theorem epsHom_comp_inl {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (epsHom φ).comp (TrivSqZeroExt.inlAlgHom R D D) = (TrivSqZeroExt.inlAlgHom R D' D').comp φ := by
  ext r
  · simp [epsHom, DualNumber.lift_apply_apply]
  · simp [AlgHom.comp_apply, snd_epsHom]

theorem epsHom_comp_epsMap {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (epsHom φ).comp (EpsWeil.epsMap R D) = EpsWeil.epsMap R D' := by
  apply DualNumber.algHom_ext
  simp [epsHom, EpsWeil.epsMap, DualNumber.lift_apply_apply]

theorem ptV_eq {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D]
    (x : Pt A D) : ptV v x = (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x) *
      (spOver (EpsWeil.epsMap R D) ≫ CartesianMonoidalCategory.lift 1 v) := by
  ext1 <;> simp [ptV, pt0, MonObj.mul_comp, comp_lift, MonObj.comp_one]

theorem specOverOfAlgHom_comp_pointWithZeroSecondCoord {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {D D' : Type} [CommRing D] [Algebra R D] [CommRing D']
    [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) : spOver φ ≫ pt0 B x = pt0 B (spOver φ ≫ x) := by
  simp [pt0, comp_lift]

theorem cohom_sndPull_zero : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (f : Z1 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR (A ⊗ B) →
    ∀ v : epsR R ⟶ B, Cohom (whole A) (sndPull (fv f) v) (Fn1.zero A) := by
  intro R _ A B _ _ f hf v
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass R (A ⊗ B) f hf
  have hc := (GlobalTheory.T.crystallineCocycleOnPoints_isCocycle_and_eval_eq R (A ⊗ B) f).1
  let V1 : Pt (A ⊗ B) (DualNumber R) := CartesianMonoidalCategory.lift 1 v
  refine ⟨fun D _ _ x ↦ (g (DualNumber D) (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x)
      (spOver (EpsWeil.epsMap R D) ≫ V1) +
      fv f D (DualNumber D) (TrivSqZeroExt.inlAlgHom R D D) (pt0 B x) +
      fv f (DualNumber R) (DualNumber D) (EpsWeil.epsMap R D) V1).snd, ?_⟩
  intro D _ _ D' _ _ φ x _
  have e1 := hg (DualNumber D) (DualNumber D') (epsHom φ) (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x)
    (spOver (EpsWeil.epsMap R D) ≫ V1)
  rw [← ptV_eq] at e1
  have hX : spOver (epsHom φ) ≫ spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x =
      spOver (TrivSqZeroExt.inlAlgHom R D' D') ≫ pt0 B (spOver φ ≫ x) := by
    rw [← Category.assoc, spOver_comp, epsHom_comp_inl, ← spOver_comp, Category.assoc, specOverOfAlgHom_comp_pointWithZeroSecondCoord]
  have hV : spOver (epsHom φ) ≫ spOver (EpsWeil.epsMap R D) ≫ V1 = spOver (EpsWeil.epsMap R D') ≫ V1 := by
    rw [← Category.assoc, spOver_comp, epsHom_comp_epsMap]
  rw [hX, hV] at e1
  have c1 := hc D (DualNumber D) (DualNumber D') (TrivSqZeroExt.inlAlgHom R D D) (epsHom φ) (pt0 B x)
    (sm_whole _)
  have c2 := hc D D' (DualNumber D') φ (TrivSqZeroExt.inlAlgHom R D' D') (pt0 B x) (sm_whole _)
  rw [epsHom_comp_inl, c2, specOverOfAlgHom_comp_pointWithZeroSecondCoord] at c1
  have c3 := hc (DualNumber R) (DualNumber D) (DualNumber D') (EpsWeil.epsMap R D) (epsHom φ) V1 (sm_whole _)
  rw [epsHom_comp_epsMap] at c3
  have s1 := congrArg TrivSqZeroExt.snd e1
  have s2 := congrArg TrivSqZeroExt.snd c1
  have s3 := congrArg TrivSqZeroExt.snd c3
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub, snd_epsHom, AlgHom.coe_coe, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.snd_inl, zero_add] at s1 s2 s3
  simp only [Fn1.add, Fn1.neg, Fn1.zero, sndPull, neg_zero, add_zero, TrivSqZeroExt.snd_add, map_add]
  linear_combination -s1 - s2 - s3

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorEqOfTangentDerivativeAtOriginEqStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentVector_eq_of_tangentDerivativeAtOrigin_eq : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (u v : TanM (𝟙 (Sp R)) G), (∀ f, tanDer G u f = tanDer G v f) → u = v := by
  first | exact @GlobalTheory.CoordsOrigin.tanM_eq_of_tanDer | exact GlobalTheory.CoordsOrigin.tanM_eq_of_tanDer | (intros; apply GlobalTheory.CoordsOrigin.tanM_eq_of_tanDer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauBimultOfRefinesPolarisedDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tauBimult_of_refines_polarised_data : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X), Function.Injective ρ → Half Q ρ D e (fun _ _ => 1) → D.TauBimult := by
  first | exact @GlobalTheory.PolDeg.tauBimult_of_half | exact GlobalTheory.PolDeg.tauBimult_of_half | (intros; apply GlobalTheory.PolDeg.tauBimult_of_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiIsEvenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_psi_isEven : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), Tens D.toPre D' W → D'.PsiEven := by
  first | exact @GlobalTheory.TensEven.main | exact GlobalTheory.TensEven.main | (intros; apply GlobalTheory.TensEven.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSurjectiveKerOfAffinePullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorProduct_surjective_ker_of_affine_pullback : ∀ {R O R' Q : Type} [CommRing R] [CommRing O] [CommRing R'] [CommRing Q] [Algebra R O] [Algebra R R'] [Algebra R Q] (I : Ideal R') (a : O →ₐ[R] Q) (b : R' ⧸ I →ₐ[R] Q), IsPullback (spMap (a : O →+* Q)) (spMap (b : R' ⧸ I →+* Q)) (spMap (algebraMap R O)) (spMap (algebraMap R (R' ⧸ I))) → Function.Surjective (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) = I.map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R') := by
  first | exact @GlobalTheory.Mum.tensor_of_pullback_surj_ker | exact GlobalTheory.Mum.tensor_of_pullback_surj_ker | (intros; apply GlobalTheory.Mum.tensor_of_pullback_surj_ker <;> assumption)
end

