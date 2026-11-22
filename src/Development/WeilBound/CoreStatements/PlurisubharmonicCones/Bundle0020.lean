import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0017
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginComparisonSubset
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.TendstoEpsT
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.TendstoArFun
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0045
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0182
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0025
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0132
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0040

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.HtLabelCongr
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Lat

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V : Type} [AddCommGroup V] [Module Ω V]

theorem patch_congr' (T : Finset ℕ) (L₀ : Lat ξ V) (Lp Lp' : ℕ → Lat ξ V)
    (h : ∀ p ∈ T, ∀ q, InFibre ξ p q → Lp p q = Lp' p q) : Lat.patch T L₀ Lp = Lat.patch T L₀ Lp' := by
  funext q
  simp only [Lat.patch]
  split_ifs with hF
  · refine iInf_congr fun p => iInf_congr fun hp => iInf_congr fun hq => ?_
    rw [h p hp q hq]
  · rfl

theorem vbOn_congr {L L' : Lat ξ V} {T : Set (Cpt ξ)} {r : ℕ} {U : Submodule Ω V} (h : ∀ q ∈ T, L q = L' q)
    (hL : L.IsVBOn T r U) : L'.IsVBOn T r U := by
  intro p hp
  obtain ⟨W, hW, b, hb, hf⟩ := hL p hp
  exact ⟨W, hW, b, hb, fun q hq hqW => ⟨(hf q hq hqW).1, (h q hq).symm.trans (hf q hq hqW).2⟩⟩

end Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem htLabel_congr {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) {n n' : ℕ}
    (ρ : 𝓞 E →+* Module.End Ω Li) (σ : CMType H ⊕ CMType H → (𝓞 E →+* Ω)) (s : CMType H ⊕ CMType H) {q : Cpt ξ}
    (h : M.htOm L n q = M.htOm L n' q) : htLabel M L n ρ σ s q = htLabel M L n' ρ σ s q := by
  rcases s with τ | τ
  · simp only [htLabel, LieModel.htW, LieModel.htDual, h]
  · simp only [htLabel, LieModel.htDual, h]

section Level

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S₀ : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
  {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S₀ y) (S : Finset ℕ)

theorem patch_four (h : ∀ p ∈ S, ∀ q, InFibre 𝔐.ξ p q → 𝔐.M.htOm 𝔐.t.PP.L (p ^ 4) q = 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q)
    (s : CMType H ⊕ CMType H) :
    Lat.patch S (𝔐.dR s) (fun p => htLabel 𝔐.M 𝔐.t.PP.L (p ^ 4) 𝔐.ρ 𝔐.emb s) = 𝔐.VS S s :=
  patch_congr' _ _ _ _ fun p hp q hq => htLabel_congr _ _ _ _ _ (h p hp q hq)

def levFour (hp : ∀ p ∈ S, p.Prime) (hR : ∀ p ∈ S, 4 ≤ 𝔐.R p) (ht : ∀ p ∈ S, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p))
    (hvb : ∀ s, (𝔐.VS S s).IsVB (labelRk D s) (𝔐.Vgen s))
    (h : ∀ p ∈ S, ∀ q, InFibre 𝔐.ξ p q → 𝔐.M.htOm 𝔐.t.PP.L (p ^ 4) q = 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q) :
    HodgeCpt Y S y :=
  { 𝔐 with
    S_prime := hp
    R := fun _ => 4
    R_ge := fun _ _ => le_rfl
    tors := fun p hpS k _ i g hg => ht p hpS k i g (by
      obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (hR p hpS)
      rw [hn, pow_add, pow_mul, hg, _root_.one_pow])
    vb := fun s => by
      have h1 := hvb s
      rw [← patch_four 𝔐 S h s] at h1
      exact h1 }

end Level

theorem pull_on {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω Ω' : Type} [Field Ω] [Field Ω'] {i : Ω →+* Ω'}
    {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)]
    {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'} (B : HodgeCpt Y S y) (A : HodgeCpt Y S y') (g : A.X ⟶ B.X)
    (x : Sp Ω ⟶ Xo.XF c) (hx : B.ξ ≫ B.f = x ≫ Y.j) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S)
    (hvb : ∀ p ∈ S, ∀ s, ((B.M.htOm B.t.PP.L (p ^ B.R p)).map (B.Vgen s).dualRestrict).IsVBOn {q | InFibre B.ξ p q}
      (labelRk D s) ⊤)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ B.ξ g i) (hf : g ≫ B.f = A.f) (hR : ∀ p ∈ S, A.R p = B.R p) :
    ∃ (j : B.Li →+ A.Li) (m : SABMap A.t B.t g), IsExtOver i j ∧
      (∀ a, (A.M.pt (j a)).left ≫ m.φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (B.M.pt a).left) ∧
      ∀ s, A.V s = (B.V s).pull A.ξ g j := by
  obtain ⟨A', e, j', m', p1, p2, p3, p4, p5, p6, p7, -, p9⟩ :=
    GlobalTheory.T.hodge_cpt_field_extension E H D l Xo c _ _ Y S Ω Ω' i K K' J J' y y' B x A.X A.ξ g hx hdisc hvb A.all A.tie A.normal hd
  have he : A.ξ ≫ e.symm.hom = A'.ξ := by
    rw [← p1]
    simp
  have hf' : e.symm.hom ≫ A'.f = A.f := by
    rw [p2, ← hf]
    simp
  have hc : A'.cst = A.cst := by
    refine OrLinked.ringHom_ext_int c (OrLinked.spMap_inj' ?_)
    rw [← A'.cst_over, ← A.cst_over, ← hf', ← he]
    simp only [Category.assoc]
  obtain ⟨φ, φt, -, φr, φp⟩ := OrLinked.same_base_cmp A' A e.symm he hf' hc
  have ha : (FrameRebase.sabRebase A.m hf.symm).φ = A.m.φ := FrameRebase.sabRebase_φ _ _
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H _ _ _ Y.t B.t A.t B.f g B.m (FrameRebase.sabRebase A.m hf.symm)
  rw [ha] at hk
  let j : B.Li →+ A.Li := φ.toLinearMap.toAddMonoidHom.comp j'
  have hjd : ∀ a, j a = φ (j' a) := fun _ => rfl
  have hj : IsExtOver i j := ⟨fun a v => by rw [hjd, hjd, p6.1, map_smul], fun n b hb =>
    (p6.2 n b hb).map' φ.toLinearMap φ.ker⟩
  have hd' : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ B.ξ (e.hom ≫ g) i := by
    show A'.ξ ≫ e.hom ≫ g = _
    rw [← Category.assoc, p1]
    exact hd
  refine ⟨j, k, hj, fun a => B.m.cart.1.hom_ext ?_ ?_, fun s => ?_⟩
  · show ((A.M.pt (φ (j' a))).left ≫ k.φ) ≫ B.m.φ = _
    rw [Category.assoc, ← hk, φt, p3, ← Category.assoc, p7]
  · have w1 := Over.w (A'.M.pt (j' a))
    have w2 := Over.w (A.M.pt (φ (j' a)))
    have w3 : (A'.M.pt (j' a)).left ≫ A'.t.G.hom ≫ e.hom = (A.M.pt (φ (j' a))).left ≫ A.t.G.hom := by
      rw [← Category.assoc, w1, w2, ← p1]
      exact Category.assoc _ _ _
    show ((A.M.pt (φ (j' a))).left ≫ k.φ) ≫ B.t.G.hom = _
    rw [← p7, Category.assoc, Category.assoc, k.cart.1.w, m'.cart.1.w, ← Category.assoc, ← w3]
    simp only [Category.assoc]
  · funext q
    obtain ⟨hq, -, -⟩ := RegAtDom.regAt_dominates _ _ _ _ _ _ g i hd q
    obtain ⟨U, hU, b, -, hb⟩ := B.vb s ⟨g q.1, hq⟩ trivial
    have hb1 : (B.V s).IsFrameAt b ⟨g q.1, hq⟩ := hb _ trivial hU
    have h' := OrLinked.genPt_spec e.symm he q
    have e1 : (e.hom ≫ g) (e.symm.hom q.1) = g q.1 := by simp
    have hq' : genPt B.ξ ⤳ (e.hom ≫ g) (e.symm.hom q.1) := e1 ▸ hq
    have hb2 : (B.V s).IsFrameAt b ⟨(e.hom ≫ g) (e.symm.hom q.1), hq'⟩ := by
      have : (⟨(e.hom ≫ g) (e.symm.hom q.1), hq'⟩ : Cpt B.ξ) = ⟨g q.1, hq⟩ := Subtype.ext e1
      rw [this]
      exact hb1
    have hb3 := FlagPull.pull_isFrameAt hd' p6 ⟨e.symm.hom q.1, h'⟩ hq' hb2
    rw [← p9] at hb3
    have hb4 : (A.V s).IsFrameAt (fun k => φ (j' (b k))) q :=
      OrLinked.frame_tr φ (φr q h') (φp S (fun p hp => by rw [p5]; exact hR p hp) s q h') hb3
    exact hb4.2.trans (FlagPull.pull_isFrameAt hd hj q hq hb1).2.symm

end LevelTowerAlt.Comparison₂
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.PullCst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp SheetDecomposition

noncomputable section

namespace LevelTowerAlt.Comparison₂

theorem pull_cst' {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)]
    [∀ k, Fintype (J' k)] {κ : K → K'} {v : (Σ k, J k) → Σ k, J' k} (hv : IsBlockMap κ v) :
    IsPullHerm κ v (PF.cst J) (PF.cst J') := by
  refine ⟨?_, fun z => rfl⟩
  show (0 : K' → ℤ) = pullDeg κ 0
  funext k
  by_cases hk : ∃ a, κ a = k
  · obtain ⟨a, rfl⟩ := hk
    exact (hv.1.extend_apply (0 : K → ℤ) (0 : K' → ℤ) a).symm
  · exact (Function.extend_apply' (0 : K → ℤ) (0 : K' → ℤ) _ hk).symm

theorem root_eq {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N n : ℕ} {M : Top.RootModel Ψ N}
    {S : PB.AnSys (Top.dimFl Ψ N) (Option (Ψ × Fin N))} (R : Top.RealTie M S n) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ S.t₀)
    (c : Option (Ψ × Fin N) → ℤ) :
    (Top.combLine (fun o : Option (Ψ × Fin N) => o.elim (PF.cst M.ι) (M.x t)) c).a =
      (Top.combLine (fun o : Option (Ψ × Fin N) => o.elim (PF.cst M.ι) fun r => R.Re.line (some r) t)
        fun o => o.elim (c none) (gapc (c ∘ some))).a ∧ ∀ z ∈ mcPts M.P,
    (Top.combLine (fun o : Option (Ψ × Fin N) => o.elim (PF.cst M.ι) (M.x t)) c).h z =
      (Top.combLine (fun o : Option (Ψ × Fin N) => o.elim (PF.cst M.ι) fun r => R.Re.line (some r) t)
        fun o => o.elim (c none) (gapc (c ∘ some))).h z := by
  refine ⟨?_, fun z hz => ?_⟩
  · simp only [Top.combLine, Fintype.sum_option, Option.elim, R.Re.line_deg, M.x_deg]
    congr 1
    refine (sum_gapc (c ∘ some) M.xdeg).symm.trans (Finset.sum_congr rfl fun r _ => ?_)
    rw [R.fund_deg]
  · refine Real.log_injOn_pos (HermLine.pos _ _ hz.1) (HermLine.pos _ _ hz.1) ?_
    rw [log_comb _ _ hz.1, log_comb _ _ hz.1]
    simp only [Fintype.sum_option, Option.elim, ← zsmul_eq_mul]
    congr 1
    refine (sum_gapc (c ∘ some) fun r => Real.log ((M.x t r).h z)).symm.trans (Finset.sum_congr rfl fun r _ => ?_)
    rw [R.fund_reg r.1 r.2 t h0 h1 z hz]

set_option maxHeartbeats 1000000 in
theorem tie_of (hC : Common) (hR : Replace) (hB : BaseSide) : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) := by
  intro hAg _ _ hG _ E _ _ _ _ H D Xo l c Y _ T o II _ hEx hII hp hq B B₁ a K _ J _ Ω _ _ W _ _ Dc O Lt _ _ _ X Or _ hBB hqp
    hbg hsm hGood hgen hS
  have hI : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hK : ResK.ResKStatement := hG.2.2.2.2.1
  have hSeq : o.S B = T.bad ∪ Dc.SB B := by
    ext r
    rw [o.S_iff, Top.RootTower.InS, Finset.mem_union, ComponentData.SB, Finset.mem_filter, hS]
    have := (o.bad_iff r).1
    by_cases h : r ∈ T.bad
    · simp [h, (this h).1]
    · simp only [h, or_false, false_or, not_false_eq_true, and_true]
      exact ⟨fun h => ⟨⟨h.1, h.2.trans hBB⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  obtain ⟨K₃, _, ρ, _, κ₁, v₁, κ₂, v₂, Ω₃, _, _, y, β, b, hb₁, hb₂, he₁, he₂, har, hβ, hβn, hrk, hbd, hiso⟩ :=
    hC hG E H D Xo l c Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) II K J Ω W Dc X.H T.bad Or B hSeq
      (fun p hp hd => (o.bad_iff p).2 ⟨hp, (hd.mul_left 2).mul_right _⟩) (o.omVB B a) (hEx.2 B a) hp hbg hsm hGood hgen
  have hmono := OrLinked.mono_int' c
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.hodge_component_factor_point E H D l _ c _ _ Y _ _ _ _ _ (o.Or B a).𝔐 hmono
  have alg := GlobalTheory.T.root_model_origin_compatibility E H D l _ c _ _ Y _ _ _ _ (o.Or B a) (spMap (o.Or B a).𝔐.fn ≫ x₀) (by
    rw [Category.assoc, ← hx₀]; exact (o.Or B a).𝔐.fn_over) hmono (hEx.1 a)
  have : Nonempty (RootIx D) := ⟨(Classical.choice (GlobalTheory.T.cm_host_rank_bounds E H).2.1, ⟨0, by omega⟩)⟩
  obtain ⟨K', _, ρ', _, κ, v, y', hb, hy, hfield, har', hcore⟩ := anCore hR hB hI hK hII ((o.Or B a).Re.comap some) alg
    (gapc (muExp D.p)) (Top.combLine (o.Or B a).sing (muExp D.p)) (by
      simp only [Top.combLine, (o.Or B a).sing_deg]
      refine (sum_gapc _ _).symm.trans (Finset.sum_congr rfl fun r _ => ?_)
      rw [← (o.Or B a).fund_deg]
      rfl) (fun x hx => by
      refine (log_comb _ _ ((o.Or B a).Re.R.mem x x ((o.Or B a).Re.R.mem_U x)).1).trans ?_
      simp only [← zsmul_eq_mul]
      refine (sum_gapc _ fun r => Real.log (((o.Or B a).sing r).h _)).symm.trans (Finset.sum_congr rfl fun r _ => ?_)
      exact congrArg _ ((o.Or B a).fund_sing r.1 r.2 x hx).symm) X.H X.S B X.S_tied hb₁ hb₂ he₁ he₂ har hβ hβn hbd hiso
  have hjb := GlobalTheory.T.block_join_inclusions_compat
  have hc₁ := (hjb.2.2 _ _ K₃ ρ K' ρ' κ₁ v₁ κ v hb₁ hb).1
  have hc₂ := (hjb.2.2 K J K₃ ρ K' ρ' κ₂ v₂ κ v hb₂ hb).1
  have hy₁ : y' ∘ v ∘ v₁ = y ∘ v₁ := by rw [← hy]; rfl
  have e₁ : imageZ (v ∘ v₁) (mCoordIdeal y') = (T.M B a).P := by rw [hjb.2.1 _ _ K' ρ' _ _ Ω₃ y' hc₁, hy₁, he₁]
  have e₂ : imageZ (v ∘ v₂) (mCoordIdeal y') = mCoordIdeal Dc.y := by
    rw [hjb.2.1 K J K' ρ' _ _ Ω₃ y' hc₂, ← he₂, ← hy]
    rfl
  have hp₁ := GlobalTheory.T.block_pullback_herm_line _ _ K' ρ' _ _ hc₁
  have hp₂ := GlobalTheory.T.block_pullback_herm_line K J K' ρ' _ _ hc₂
  choose pl hpl using fun A => (hp₁.1 A).exists
  choose Mt hMt using fun t => (hp₂.1 (muReg X.H X.S B t)).exists
  have hcore' := hcore Mt (fun t r => pl ((o.Or B a).Re.line (some r) t)) hMt fun t r => hpl _
  let RT := (Top.realOf o.toTowerOrigin).tie B a
  have ht₀ : 0 < (o.Sys a).t₀ := ((o.Sys a).reg none).1
  let x' : ℝ → Option (RootIx D) → HermLine (T.M B a).ι := fun t o' => o'.elim (PF.cst _) ((T.M B a).x t)
  have hx' : ∀ t cc, IsSmoothHerm (Top.combLine (x' t) cc) := fun t cc => (GlobalTheory.T.hermitian_combination_smooth_conj _ _ _ _ cc).1 fun o' => by
    cases o'
    exacts [PF.cst_smooth, (T.M B a).x_smooth _ _]
  have hreg := GlobalTheory.T.regularized_hodge_metric_smooth K J II _ Ω W Dc X.H X.M X.S B X.S_tied
  set e := IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) with he
  have key : ∀ (a' b' : ℕ) (cc : Fin b' → Option (RootIx D) → ℤ), a' + b' = Top.dimFl (CMType H) (D.p + D.q) + 1 →
      Tendsto (fun t => II K' ρ' (mCoordIdeal y') (a' + b') (Fin.append (fun _ : Fin a' => Mt t)
          fun j => pl (Top.combLine (x' t) (cc j))) - e * II _ _ (T.M B a).P (a' + b') (Fin.append
            (fun _ : Fin a' => Top.combLine ((T.M B a).x t) (muExp D.p)) fun j => Top.combLine (x' t) (cc j))) (𝓝[>] 0) (𝓝 0) := by
    intro a' b' cc hab
    refine (hcore' a' b' (fun j o' => o'.elim (cc j none) (gapc (cc j ∘ some))) hab).congr' ?_
    filter_upwards [hreg, Ioc_mem_nhdsGT ht₀] with t h1 h2
    have hA : IsArithVar (mCoordIdeal y') (a' + b') := hab ▸ har'
    have hls : ∀ cc, IsSmoothHerm (Top.combLine (fun o' : Option (RootIx D) => o'.elim (PF.cst ρ')
        fun r => pl ((o.Or B a).Re.line (some r) t)) cc) := fun cc => (GlobalTheory.T.hermitian_combination_smooth_conj _ _ _ _ cc).1 fun o' => by
      cases o'
      exacts [PF.cst_smooth, hp₁.2.1 _ _ (hpl _) ((o.Or B a).Re.line_smooth _ t h2.1 h2.2)]
    have hq : ∀ cc : Option (RootIx D) → ℤ, (Top.combLine (fun o' : Option (RootIx D) => o'.elim (PF.cst ρ')
        fun r => pl ((o.Or B a).Re.line (some r) t)) fun o' => o'.elim (cc none) (gapc (cc ∘ some))).a =
          (pl (Top.combLine (x' t) cc)).a ∧ ∀ z ∈ mcPts (mCoordIdeal y'),
        (Top.combLine (fun o' : Option (RootIx D) => o'.elim (PF.cst ρ')
        fun r => pl ((o.Or B a).Re.line (some r) t)) fun o' => o'.elim (cc none) (gapc (cc ∘ some))).h z =
          (pl (Top.combLine (x' t) cc)).h z := by
      intro cc
      have h3 := (GlobalTheory.T.iso_line_on_equivalence K' ρ' _ ∅ har'.2.1 (Set.empty_subset _)).2.2.2 _ _ _ _ _
        (fun o' : Option (RootIx D) => o'.elim (PF.cst _) fun r => (o.Or B a).Re.line (some r) t)
        (fun o' : Option (RootIx D) => o'.elim (PF.cst ρ') fun r => pl ((o.Or B a).Re.line (some r) t))
        (fun o' => o'.elim (cc none) (gapc (cc ∘ some))) hc₁ fun o' => by
          cases o'
          exacts [pull_cst' hc₁, hpl _]
      have h4 := root_eq RT h2.1 h2.2 cc
      exact ⟨h3.1.trans ((congrArg _ h4.1.symm).trans (hpl _).1.symm),
        fun z hz => (h3.2 z).trans ((h4.2 _ (e₁ ▸ hp₁.2.2.1 _ _ hz)).symm.trans ((hpl _).2 z).symm)⟩
    have hm := hq fun o' => o'.elim 0 (muExp D.p)
    rw [comb_some] at hm
    have hMs := hp₂.2.1 _ _ (hMt t) h1.1
    have hxs := (GlobalTheory.T.hermitian_combination_smooth_conj _ _ _ _ (muExp D.p)).1 ((T.M B a).x_smooth t)
    congr 1
    · refine hI.metricLocal K' ρ' _ (hII.1 K' ρ') _ _ _ _ hA ?_ ?_ ?_ ?_ <;> refine Fin.addCases (fun j => ?_) fun j => ?_ <;>
        simp only [Fin.append_left, Fin.append_right]
      exacts [hMs, hls _, hMs, hp₁.2.1 _ _ (hpl _) (hx' _ _), (hq _).1, fun _ _ => trivial, (hq _).2]
    · have h5 := hII.2.2.1 _ _ K' ρ' _ _ Ω₃ y' (a' + b') (Fin.append
          (fun _ : Fin a' => Top.combLine ((T.M B a).x t) (muExp D.p)) fun j => Top.combLine (x' t) (cc j))
        (Fin.append (fun _ : Fin a' => pl (Top.combLine ((T.M B a).x t) (muExp D.p))) fun j => pl (Top.combLine (x' t) (cc j)))
        hc₁ hA (by rw [e₁, hab]; exact (T.M B a).arith)
        (Fin.addCases (fun j => by simpa using hxs) fun j => by simpa using hx' _ _)
        (Fin.addCases (fun j => by simpa using hpl _) fun j => by simpa using hpl _)
      rw [e₁, hy₁, hfield] at h5
      rw [← h5]
      refine hI.metricLocal K' ρ' _ (hII.1 K' ρ') _ _ _ _ hA ?_ ?_ ?_ ?_ <;> refine Fin.addCases (fun j => ?_) fun j => ?_ <;>
        simp only [Fin.append_left, Fin.append_right]
      exacts [hls _, hls _, hp₁.2.1 _ _ (hpl _) hxs, hp₁.2.1 _ _ (hpl _) (hx' _ _), hm.1, (hq _).1, hm.2, (hq _).2]
  let ee := (Fintype.equivFin (PairIx (CMType H) D.p D.q)).symm
  have hdim : Dc.n + Fintype.card (PairIx (CMType H) D.p D.q) = Top.dimFl (CMType H) (D.p + D.q) := by
    rw [Or.n_eq, count_pairs]
  let cF := fun i (o' : Option (RootIx D)) => o'.elim 0 (fibCoef (ee i))
  have hδ : (0 : ℝ) < e * (T.M B a).δ := mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hrk)) (Nat.cast_pos.2 (T.M B a).δ_pos)
  have happ : ∀ (t : ℝ) (n : ℕ), (Fin.append (fun _ : Fin n => Top.combLine ((T.M B a).x t) (muExp D.p))
      fun j => Top.combLine (x' t) (cF j)) = fun j => Top.combLine ((T.M B a).x t)
        (Fin.append (fun _ : Fin n => muCoef (CMType H) D.p D.q) (fun j => fibCoef (ee j)) j) := by
    intro t n
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp only [Fin.append_left, Fin.append_right]
    · rfl
    · exact comb_some _ _ _
  have hNa : ∀ t i, (pl (Top.combLine (x' t) (cF i))).a = (pl (Top.combLine (x' 1) (cF i))).a := fun t i => by
    rw [(hpl _).1, (hpl _).1, comb_some, comb_some]
    simp only [Top.combLine, (T.M B a).x_deg]
  have hNs : ∀ t i, IsSmoothHerm (pl (Top.combLine (x' t) (cF i))) := fun t i => hp₁.2.1 _ _ (hpl _) (hx' _ _)
  refine ⟨K', inferInstance, ρ', inferInstance, κ ∘ κ₂, v ∘ v₂, mCoordIdeal y', _, 1, fun _ => 1, Mt,
    fun t _ i => pl (Top.combLine (x' t) (cF i)), e * (T.M B a).δ, hc₂, by rw [Nat.add_right_comm, hdim]; exact har', e₂, hδ,
    fun t _ i => hNa t i, fun t _ i => hNs t i, Eventually.of_forall hMt, ?_, ?_⟩
  · have h1 := key (Dc.n + 1) _ cF (by rw [Nat.add_right_comm, hdim])
    have h2 := (tendsto_arFun (T.M B a) ((GlobalTheory.T.real_tower_conv_I2 hAg hI II hII _ _ T (Top.realOf o.toTowerOrigin)).1 B a)
      (Top.toA (Top.testPoly T.j))).const_mul (e * (T.M B a).δ : ℝ)
    have h3 := h1.add h2
    rw [zero_add] at h3
    refine h3.congr fun t => ?_
    rw [happ, ← arFun_prod (T.M B a) hII t (by rw [Nat.add_right_comm, hdim]), ← test_factor' ee hqp Or.n_eq, o.j_eq]
    simp only [Finset.univ_unique, Finset.sum_singleton, _root_.one_mul]
    ring
  · have h1 := key Dc.n _ (Fin.snoc (α := fun _ => Option (RootIx D) → ℤ) cF fun o' => o'.elim 1 0) (by rw [← hdim]; rfl)
    have hA : IsArithVar (mCoordIdeal y') (Dc.n + Fintype.card (PairIx (CMType H) D.p D.q) + 1) := hdim ▸ har'
    have hs : ∀ t t', IsSmoothHerm (muReg X.H X.S B t) → ∀ j, IsSmoothHerm (Fin.append (fun _ : Fin Dc.n => Mt t)
        (fun i => pl (Top.combLine (x' t') (cF i))) j) := fun t t' ht =>
      Fin.addCases (fun j => by simpa using hp₂.2.1 _ _ (hMt t) ht) fun j => by simpa using hNs _ _
    have hcst : ∀ t t' u u', IsSmoothHerm (muReg X.H X.S B t) → IsSmoothHerm (muReg X.H X.S B u) →
        ptsIntegral (mCoordIdeal y') (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t)
          (fun i => pl (Top.combLine (x' t') (cF i))) i).h z)) (fun _ => 1) =
        ptsIntegral (mCoordIdeal y') (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt u)
          (fun i => pl (Top.combLine (x' u') (cF i))) i).h z)) (fun _ => 1) := fun t t' u u' ht hu =>
      pts_deg hI hA (hs t t' ht) (hs u u' hu) (Fin.addCases (fun j => by
        simp only [Fin.append_left, (hMt _).1, muReg, smoothRep_a]
        rfl) fun j => by simp only [Fin.append_right, hNa])
    filter_upwards [hreg] with u hu
    simp only [Finset.univ_unique, Finset.sum_singleton, _root_.one_mul]
    refine sub_eq_zero.1 (neg_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds (h1.congr' ?_)))
    filter_upwards [hreg] with t ht
    have a1 : (fun j => pl (Top.combLine (x' t) (Fin.snoc (α := fun _ => Option (RootIx D) → ℤ) cF (fun o' => o'.elim 1 0) j))) =
        Fin.snoc (α := fun _ => HermLine ρ') (fun j => pl (Top.combLine (x' t) (cF j))) (PF.cst ρ') := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [comb_none]
      exact (hp₁.1 _).unique (hpl _) (pull_cst' hc₁)
    have a2 : (fun j => Top.combLine (x' t) (Fin.snoc (α := fun _ => Option (RootIx D) → ℤ) cF (fun o' => o'.elim 1 0) j)) =
        Fin.snoc (α := fun _ => HermLine (T.M B a).ι) (fun j => Top.combLine (x' t) (cF j)) (PF.cst _) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
      exact comb_none _ _
    rw [a1, a2, Fin.append_snoc, Fin.append_snoc, happ]
    have a3 := LevelTowerAlt.ii_cst_int hII.1 hA _ (hs t t ht.1)
    have a4 := LevelTowerAlt.ii_cst_int hII.1 (show IsArithVar (T.M B a).P _ from hdim ▸ (T.M B a).arith)
      (fun j => Top.combLine ((T.M B a).x t)
        (Fin.append (fun _ : Fin Dc.n => muCoef (CMType H) D.p D.q) (fun j => fibCoef (ee j)) j))
      fun j => (GlobalTheory.T.hermitian_combination_smooth_conj _ _ _ _ _).1 ((T.M B a).x_smooth t)
    rw [← geoFun_pts (T.M B a) hI t hdim, ← test_factor ee hqp Or.n_eq] at a4
    rw [hcst t t u 1 ht.1 hu.1] at a3
    refine (congrArg₂ (fun r s : ℝ => r - e * s) a3 a4).trans ?_
    rw [o.j_eq]
    ring

end LevelTowerAlt.Comparison₂
end
end

