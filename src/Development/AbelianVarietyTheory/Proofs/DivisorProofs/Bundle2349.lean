import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDataTateSpan
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
namespace GlobalTheory.FlatModel.EigSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] {P : PtP E p} {V : Type} [CommRing V]

noncomputable def phi (β : V →+* 𝓞_ℂ_[p]) (tι : Dw.La →+ P.T) : V ⊗[ℤ] Dw.La →ₗ[ℤ] P.V :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun (v : V) (b : Dw.La) => ((β v : 𝓞_ℂ_[p]) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι b)
    (fun v v' b => by simp [TensorProduct.add_tmul])
    (fun n v b => by simp [TensorProduct.smul_tmul'])
    (fun v b b' => by simp [TensorProduct.tmul_add])
    (fun n v b => by simp [TensorProduct.tmul_smul]))

theorem phi_tmul (β : V →+* 𝓞_ℂ_[p]) (tι : Dw.La →+ P.T) (v : V) (b : Dw.La) :
    phi β tι (v ⊗ₜ b) = ((β v : 𝓞_ℂ_[p]) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι b := by
  unfold phi
  erw [TensorProduct.lift.tmul]; rfl

theorem phi_smul (β : V →+* 𝓞_ℂ_[p]) (tι : Dw.La →+ P.T) (v : V) (y : V ⊗[ℤ] Dw.La) :
    phi β tι (v • y) = ((β v : 𝓞_ℂ_[p]) : ℂ_[p]) • phi β tι y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b =>
    rw [TensorProduct.smul_tmul', phi_tmul, phi_tmul, TensorProduct.smul_tmul']
    simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem le_span_of_casimir (β : V →+* 𝓞_ℂ_[p]) (σ : 𝓞 E →+* V) {J : Type} [DecidableEq J] {N : ℕ}
    (a : Fin N → Dw.La) (T S : J → Fin N → V) (tι : Dw.La →+ P.T) (hL : LatData Dw σ a T S)
    (hι : ∀ (o : 𝓞 E) b, tι (o • b) = P.actT o (tι b))
    (hsp : Submodule.span ℤ_[p] (Set.range tι) = ⊤)
    {d : ℕ} (c θ : Fin d → 𝓞 E) (hc : ∀ o : 𝓞 E, ∑ j, c j ⊗ₜ[ℤ] (o * θ j) = ∑ j, (o * c j) ⊗ₜ[ℤ] θ j)
    (hne : ((β (σ (∑ j, c j * θ j)) : 𝓞_ℂ_[p]) : ℂ_[p]) ≠ 0) :
    P.eigV (β.comp σ) ≤
      Submodule.span ℂ_[p] (Set.range fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι (a m)) := by
  set Sp := Submodule.span ℂ_[p] (Set.range fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι (a m)) with hSp
  let χ : 𝓞 E → ℂ_[p] := fun o => ((β (σ o) : 𝓞_ℂ_[p]) : ℂ_[p])
  let Q : P.V →ₗ[ℂ_[p]] P.V := ∑ j, χ (c j) • P.actV (θ j)
  have hΦ : ∀ y ∈ Submodule.span V (Set.range fun i => ∑ m, T i m ⊗ₜ[ℤ] a m), phi β tι y ∈ Sp := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [map_sum]
      simp only [phi_tmul]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Sp.add_mem hx hy
    | smul v x _ hx => rw [phi_smul]; exact Sp.smul_mem _ hx
  have hb : ∀ b : Dw.La, Q (1 ⊗ₜ tι b) ∈ Sp := by
    intro b
    let g : 𝓞 E →ₗ[ℤ] Dw.La := (LinearMap.toSpanSingleton (𝓞 E) Dw.La b).restrictScalars ℤ
    have hx : (∑ j, σ (c j) ⊗ₜ[ℤ] (θ j • b)) ∈
        Submodule.span V (Set.range fun i => ∑ m, T i m ⊗ₜ[ℤ] a m) := by
      apply hL.2.2
      intro o
      have h1 := congrArg (TensorProduct.map σ.toIntAlgHom.toLinearMap g) (hc o)
      simp only [map_sum, TensorProduct.map_tmul] at h1
      simp only [map_sum, LinearMap.baseChange_tmul, Finset.smul_sum, TensorProduct.smul_tmul']
      simp only [g, LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply, mul_smul, map_mul,
        AlgHom.toLinearMap_apply] at h1
      exact h1
    have h2 := hΦ _ hx
    convert h2 using 1
    simp [Q, LinearMap.sum_apply, Point.actV, GlobalTheory.EigenSplit.baseChangeAction_apply,
      LinearMap.baseChange_tmul, hι, TensorProduct.smul_tmul', phi_tmul, χ]
  have hall : ∀ w, Q w ∈ Sp := by
    have hsm : ∀ (r : ℤ_[p]) (t : P.T), (1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] (r • t) =
        (algebraMap ℤ_[p] ℂ_[p] r) • ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] t) := by
      intro r t
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one, smul_eq_mul, _root_.mul_one]
    let M : Submodule ℤ_[p] P.T :=
      { carrier := {t | Q ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] t) ∈ Sp}
        add_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq, TensorProduct.tmul_add, map_add] at hx hy ⊢
          exact Sp.add_mem hx hy
        zero_mem' := by simp
        smul_mem' := fun r t ht => by
          simp only [Set.mem_setOf_eq, hsm, map_smul] at ht ⊢
          exact Sp.smul_mem _ ht }
    have hM : M = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      exact hb b
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul z t =>
      have ht : t ∈ M := hM ▸ Submodule.mem_top
      have he : z ⊗ₜ[ℤ_[p]] t = z • ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] t) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [he, map_smul]
      exact Sp.smul_mem _ ht
    | add x y hx hy => rw [map_add]; exact Sp.add_mem hx hy
  intro w hw
  have hw' := GlobalTheory.EigenSplit.mem_eigenSub.1 hw
  have hQ : Q w = χ (∑ j, c j * θ j) • w := by
    simp only [Q, LinearMap.sum_apply, LinearMap.smul_apply, hw', smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    simp [χ, map_sum, map_mul]
  have : w = (χ (∑ j, c j * θ j))⁻¹ • Q w := by
    rw [hQ, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [this]
  exact Sp.smul_mem _ (hall w)

theorem eigV_le_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (V : Type) [CommRing V]
    (β : V →+* 𝓞_ℂ_[p]) (σ : 𝓞 E →+* V) (J : Type) [DecidableEq J] (N : ℕ) (a : Fin N → Dw.La)
    (T S : J → Fin N → V) (tι : Dw.La →+ P.T), LatData Dw σ a T S → (∀ (o : 𝓞 E) b, tι (o • b) = P.actT o (tι b)) →
    Submodule.span ℤ_[p] (Set.range tι) = ⊤ →
    P.eigV (β.comp σ) ≤ Submodule.span ℂ_[p] (Set.range fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι (a m)) := by
  intro E _ _ _ H Dw p _ _ P V _ β σ J _ N a T S tι hL hι hsp
  obtain ⟨d, c, θ, hc, hne⟩ := GlobalTheory.T.exists_nonzero_trace_element E
  refine le_span_of_casimir β σ a T S tι hL hι hsp c θ hc ?_
  have hinj := GlobalTheory.ringHom_integers_injective_of_charZero E ℂ_[p] ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (β.comp σ))
  intro h
  apply hne
  apply hinj
  simpa using h

end GlobalTheory.FlatModel.EigSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismUnipotentFixesComplexPointEqOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.UnipFree

theorem free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ «γ» : LevelAut Dw l, UnipAt I «γ» → ∀ y : FrPt Xo c ℂ, ptF (move Xo c «γ» y) = ptF y → «γ» = 1 := by
  intro E _ _ _ H Dw l Xo c hpq hA1 I g hN hMb «γ» hU y hy
  have hA : l.A.Coprime l.M := by rw [hA1]; exact Nat.coprime_one_left _
  obtain ⟨ρ, ν, hiso, hm, hf⟩ := GlobalTheory.LevDesc.levR_move (Xo := Xo) (c := c) hpq hA «γ» y
  have hm' : IsLevMove ρ ν (liftLa «γ») LinearMap.id := hm
  have hx : y.x ≫ ρ = y.x := by
    have e := congrArg (· ≫ pullback.fst _ _) hy
    simp only [GlobalTheory.AllWt.ptF, pullback.lift_fst] at e
    rw [← hf.1]; exact e
  obtain ⟨hg, hnorm, hsq, hr⟩ := hN
  set x := y.x with hxdef
  set G := Xo.univ.t.G with hGdef
  let G0 : Over (Sp ℂ) := (Over.pullback x).obj G
  let act0 : OAct (𝓞 E) G0 := OAct.pullback x G Xo.univ.t.act
  have w : (pullback.fst G.hom x ≫ ν.φ) ≫ G.hom = pullback.snd G.hom x ≫ x := by
    rw [Category.assoc, ν.cart.1.w, ← Category.assoc, pullback.condition, Category.assoc, hx]
  let α : G0 ⟶ G0 := Over.homMk (pullback.lift (pullback.fst G.hom x ≫ ν.φ) (pullback.snd G.hom x) w)
    (pullback.lift_snd _ _ _)
  have hαf : α.left ≫ pullback.fst G.hom x = pullback.fst G.hom x ≫ ν.φ := pullback.lift_fst _ _ _
  have pA : IsGrpPullback G0 G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have c₁ : IsGrpPullback G0 G x (pullback.fst G.hom x ≫ ν.φ) := by
    have c₀ := IsGrpPullback.comp pA ν.cart
    rw [hx] at c₀
    exact c₀
  have hαm : IsMonHom α :=
    ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback c₁ pA (𝟙 G) α (by simpa using hαf)
  have hact0 : ∀ a, (act0.act a).left ≫ pullback.fst G.hom x = pullback.fst G.hom x ≫ (Xo.univ.t.act.act a).left :=
    fun a => pullback.lift_fst _ _ _
  have hact : ∀ a, act0.act a ≫ α = α ≫ act0.act a := fun a => by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · calc (act0.act a ≫ α).left ≫ pullback.fst G.hom x
          = (act0.act a).left ≫ (α.left ≫ pullback.fst G.hom x) := by rw [Over.comp_left, Category.assoc]
        _ = ((act0.act a).left ≫ pullback.fst G.hom x) ≫ ν.φ := by rw [hαf, Category.assoc]
        _ = pullback.fst G.hom x ≫ ((Xo.univ.t.act.act a).left ≫ ν.φ) := by rw [hact0, Category.assoc]
        _ = pullback.fst G.hom x ≫ (ν.φ ≫ (Xo.univ.t.act.act a).left) :=
          congrArg (pullback.fst G.hom x ≫ ·) (ν.act a)
        _ = (α.left ≫ pullback.fst G.hom x) ≫ (Xo.univ.t.act.act a).left := by rw [hαf, Category.assoc]
        _ = α.left ≫ ((act0.act a).left ≫ pullback.fst G.hom x) := by rw [hact0, Category.assoc]
        _ = (α ≫ act0.act a).left ≫ pullback.fst G.hom x := by rw [Over.comp_left, Category.assoc]
    · have h1 : ∀ f : G0 ⟶ G0, f.left ≫ pullback.snd G.hom x = pullback.snd G.hom x := fun f => Over.w f
      simp only [Over.comp_left, Category.assoc, h1]
  obtain ⟨n, hn, hνn⟩ := GlobalTheory.T.exists_finite_order_levelMove_universalSemiAbelian E H Dw l Xo c «γ» ρ ν hpq hA1 hiso hm'
  have hαn : (fun f => f ≫ α)^[n] (𝟙 G0) = 𝟙 G0 := by
    have key : ∀ j, ((fun f => f ≫ α)^[j] (𝟙 G0)).left ≫ pullback.fst G.hom x =
        pullback.fst G.hom x ≫ (fun f : G.left ⟶ G.left => f ≫ ν.φ)^[j] (𝟙 _) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Over.comp_left, Category.assoc, hαf,
          ← Category.assoc, ih, Category.assoc]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [key, hνn, Over.id_left, Category.id_comp, Category.comp_id]
    · have h1 : ∀ f : G0 ⟶ G0, f.left ≫ pullback.snd G.hom x = pullback.snd G.hom x := fun f => Over.w f
      rw [h1]; simp

  have bw : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (u.left ≫ pullback.fst G.hom x) ≫ G.hom = (Over.mk x).hom := fun u => by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have e : u.left ≫ pullback.snd G.hom x = 𝟙 _ := Over.w u
    rw [e, Category.id_comp]; rfl
  let B : (𝟙_ (Over (Sp ℂ)) ⟶ G0) → (Over.mk x ⟶ G) := fun u => Over.homMk (u.left ≫ pullback.fst G.hom x) (bw u)
  have B_left : ∀ u, (B u).left = u.left ≫ pullback.fst G.hom x := fun u => rfl
  have B_inj : Function.Injective B := fun u v h => by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congrArg (fun z => z.left) h
    · exact (Over.w u).trans (Over.w v).symm
  have B_mul : ∀ u v, B (u * v) = B u * B v := fun u v => by
    apply Over.OverMorphism.ext
    have e1 := pA.2 (𝟙_ _) u v (pushPt pA.1.w u) (pushPt pA.1.w v) rfl rfl
    have e2 := mul_left_congr (Category.id_comp x) (pushPt pA.1.w u) (pushPt pA.1.w v) (B u) (B v) rfl rfl
    exact e1.symm.trans e2
  let Bh : (𝟙_ (Over (Sp ℂ)) ⟶ G0) →* (Over.mk x ⟶ G) := MonoidHom.mk' B B_mul
  have B_act : ∀ u a, B (u ≫ act0.act a) = B u ≫ Xo.univ.t.act.act a := fun u a => by
    apply Over.OverMorphism.ext
    rw [B_left, Over.comp_left, Over.comp_left, B_left, Category.assoc, Category.assoc, hact0]
  have B_α : ∀ u, (B (u ≫ α)).left = (B u).left ≫ ν.φ := fun u => by
    rw [B_left, B_left, Over.comp_left, Category.assoc, hαf, Category.assoc]
  have B_one : B 1 = 1 := map_one Bh

  have tl : (toUnit (Over.mk x)).left = x := by simpa using Over.w (toUnit (Over.mk x))
  let β : KA l →+* ℂ := (algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom
  obtain ⟨-, TI, -, -, hTI⟩ := Xo.univ.geom ℂ x β y.x_over
  let et : Dw.La → (Over.mk x ⟶ G) := fun b => toUnit (Over.mk x) ≫ Xo.univ.eta b
  have et_add : ∀ a b, et (a + b) = et a * et b := fun a b => by
    simp only [et, Xo.univ.eta_add, MonObj.comp_mul]
  have et_ker : ∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La), et a = 1 := fun a ha => by
    simp only [et, Xo.univ.eta_ker a ha, MonObj.comp_one]
  have hadd : ∀ (a b : 𝓞 E) (z : Over.mk x ⟶ G), z ≫ Xo.univ.t.act.act (a + b) =
      (z ≫ Xo.univ.t.act.act a) * (z ≫ Xo.univ.t.act.act b) := fun a b z => by
    rw [Xo.univ.t.act.add, MonObj.comp_mul]
  have hone : ∀ z : Over.mk x ⟶ G, z ≫ Xo.univ.t.act.act 1 = z := fun z => by
    rw [Xo.univ.t.act.one, Category.comp_id]
  have hnat : ∀ (k : ℕ) (z : Over.mk x ⟶ G), z ≫ Xo.univ.t.act.act (k : 𝓞 E) = z ^ k := by
    intro k z
    induction k with
    | zero =>
      have h0 := hadd 0 0 z
      rw [add_zero] at h0
      simpa using h0
    | succ k ih => rw [Nat.cast_succ, hadd, ih, hone, pow_succ]
  obtain ⟨t, ht, htor⟩ := GlobalTheory.T.tateIsometry_torsion_eq_level_smul E H Dw l ℂ (Over.mk x ⟶ G) (fun a z => z ≫ Xo.univ.t.act.act a) _ TI et I g
    hadd hone hnat (fun a ha => hTI a ha) hg hnorm hsq hMb

  have tor_B : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) → ∃ c' : Dw.La, B u = et (t • c') :=
    fun u hu => htor (B u) fun a ha => by rw [← B_act, hu a ha, B_one]
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.natCard_quot_smul_le_pow_finrank E Dw.La Dw.fin Dw.proj I g hg hnorm
  classical
  haveI : Fintype (Dw.La ⧸ I • (⊤ : Submodule (𝓞 E) Dw.La)) := Fintype.ofFinite _
  let rep := Function.surjInv (Submodule.Quotient.mk_surjective (I • (⊤ : Submodule (𝓞 E) Dw.La)))
  let S' : Finset (Over.mk x ⟶ G) := Finset.univ.image fun q => et (t • rep q)
  have et_t : ∀ c', et (t • c') ∈ S' := fun c' => by
    refine Finset.mem_image.2 ⟨Submodule.Quotient.mk c', Finset.mem_univ _, ?_⟩
    have e : rep (Submodule.Quotient.mk c') - c' ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) :=
      (Submodule.Quotient.eq _).1 (Function.surjInv_eq _ _)
    have e2 := ht _ e
    rw [smul_sub] at e2
    have e3 : et (t • rep (Submodule.Quotient.mk c')) =
        et (t • rep (Submodule.Quotient.mk c') - t • c') * et (t • c') := by
      rw [← et_add, sub_add_cancel]
    rw [e3, et_ker _ e2, _root_.one_mul]
  let T0 : Finset (𝟙_ (Over (Sp ℂ)) ⟶ G0) := S'.preimage B B_inj.injOn
  have hT0 : T0.card ≤ g ^ (Dw.p + Dw.q) := by
    calc T0.card ≤ S'.card :=
          Finset.card_le_card_of_injOn B (fun u hu => Finset.mem_preimage.1 hu) B_inj.injOn
      _ ≤ (Finset.univ : Finset (Dw.La ⧸ I • (⊤ : Submodule (𝓞 E) Dw.La))).card := Finset.card_image_le
      _ = Nat.card (Dw.La ⧸ I • (⊤ : Submodule (𝓞 E) Dw.La)) := by
          rw [Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ g ^ (Dw.p + Dw.q) := by rw [← Dw.rank]; exact hcard
  have hmemT : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) → u ∈ T0 := fun u hu => by
    obtain ⟨c', hc'⟩ := tor_B u hu
    exact Finset.mem_preimage.2 (hc' ▸ et_t c')

  obtain ⟨m, hmU⟩ := GlobalTheory.T.isUnipotentModIdeal_liftLa_inv E H Dw l I «γ» hMb hU
  have hδ : ∀ b, et (liftLa «γ» (liftLa «γ»⁻¹ b)) = et b := fun b => by
    have e1 := GlobalTheory.LevelActionLaws.liftLa_mul_sub «γ» «γ»⁻¹ b
    have e2 := GlobalTheory.LevelActionLaws.liftLa_one_sub (D := Dw) (l := l) b
    rw [mul_inv_cancel] at e1
    have e3 : liftLa «γ» (liftLa «γ»⁻¹ b) - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have e4 := Submodule.sub_mem _ e2 e1
      rwa [sub_sub_sub_cancel_left] at e4
    have e5 : et (liftLa «γ» (liftLa «γ»⁻¹ b)) = et (liftLa «γ» (liftLa «γ»⁻¹ b) - b) * et b := by
      rw [← et_add, sub_add_cancel]
    rw [e5, et_ker _ e3, _root_.one_mul]
  have B_step : ∀ u b, B u = et b → B (u ≫ α) = et (liftLa «γ»⁻¹ b) := fun u b hb => by
    apply Over.OverMorphism.ext
    rw [B_α, hb, ← hδ b]
    show (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ» (liftLa «γ»⁻¹ b))).left ≫ ν.φ =
      (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ»⁻¹ b)).left
    rw [Over.comp_left, Over.comp_left, Category.assoc, hm'.2.1, tl, ← Category.assoc, hx]
  let φf : (𝟙_ (Over (Sp ℂ)) ⟶ G0) → (𝟙_ (Over (Sp ℂ)) ⟶ G0) := fun z => (z ≫ α) * z⁻¹
  have B_iter : ∀ j u b, B u = et b → B (φf^[j] u) = et (((liftLa «γ»⁻¹ - 1) ^ j) b) := by
    intro j
    induction j with
    | zero => intro u b hb; simpa using hb
    | succ j ih =>
      intro u b hb
      rw [Function.iterate_succ_apply']
      have h1 := ih u b hb
      set b' := ((liftLa «γ»⁻¹ - 1) ^ j) b
      show Bh ((φf^[j] u ≫ α) * (φf^[j] u)⁻¹) = _
      rw [map_mul, map_inv]
      show B (φf^[j] u ≫ α) * (B (φf^[j] u))⁻¹ = _
      rw [B_step _ _ h1, h1, pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
      rw [eq_comm, eq_mul_inv_iff_mul_eq, ← et_add, sub_add_cancel]
  have hunip : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) →
      (fun z : 𝟙_ (Over (Sp ℂ)) ⟶ G0 => (z ≫ α) * z⁻¹)^[m] u = 1 := fun u hu => by
    obtain ⟨c', hc'⟩ := tor_B u hu
    apply B_inj
    rw [B_iter m u _ hc', B_one, map_smul]
    exact et_ker _ (ht _ (hmU c'))
  have hαid : α = 𝟙 G0 := GlobalTheory.T.exists_small_torsion_set_for_endomorphism E ℂ G0 act0 α n m g (Dw.p + Dw.q) I
    (IsSemiAbelian.pullback x G Xo.univ.t.semi) hαm hact hn hαn hg hnorm hsq hr ⟨T0, hT0, hmemT⟩ hunip

  have hαl : α.left = 𝟙 _ := by rw [hαid]; rfl
  have fix : ∀ s : Over.mk x ⟶ G, s.left ≫ ν.φ = s.left := fun s => by
    have hs : s.left ≫ G.hom = 𝟙 (Sp ℂ) ≫ x := by rw [Category.id_comp]; exact Over.w s
    have e0 : pullback.lift s.left (𝟙 _) hs ≫ pullback.fst G.hom x = s.left := pullback.lift_fst _ _ _
    rw [← e0, Category.assoc, ← hαf, hαl, Category.id_comp]
  have heq : ∀ a, liftLa «γ» a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := fun a => by
    refine GlobalTheory.LevelFree.eta_injective Xo x β y.x_over _ ?_
    have e1 : et (liftLa «γ» a) = et a := by
      apply Over.OverMorphism.ext
      rw [← fix (et (liftLa «γ» a))]
      show (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ» a)).left ≫ ν.φ =
        (toUnit (Over.mk x) ≫ Xo.univ.eta a).left
      rw [Over.comp_left, Over.comp_left, Category.assoc, hm'.2.1, tl, ← Category.assoc, hx]
    have e2 : et (liftLa «γ» a) = et (liftLa «γ» a - a) * et a := by rw [← et_add, sub_add_cancel]
    rw [e1] at e2
    exact mul_eq_right.1 e2.symm
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have e := liftLa_spec «γ» a
  simp only [Submodule.mkQ_apply] at e
  change «γ» (Submodule.Quotient.mk a) = Submodule.Quotient.mk a
  rw [← e]
  exact (Submodule.Quotient.eq _).2 (heq a)

end GlobalTheory.UnipFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFlagEqOfPluckerPointsEqFieldPointsStatement
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieFlag_eq_of_pluckerPoints_eq_field_points : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U) (t : ∀ (σ : E →+* ℂ) (m : Fin (Dw.mult σ)), Fin (plkNum Mc m + 1) → ((F.LL (ind σ m)).pull g).Sec), (∀ σ m q, (t σ m q).f = plkLoc F Mc g hg σ m q) → ∀ (ht : ∀ σ m, ⨆ q, nonzeroLocus (t σ m q) = ⊤) {R : Type} [CommRing R] (f : T ⟶ Sp R) (K : Type) [Field K] (a a' : Sp K ⟶ T), a ≫ g ≫ π = a' ≫ g ≫ π → (∀ σ m, a ≫ GlobalTheory.ProjSpace.toProj f (t σ m) (ht σ m) = a' ≫ GlobalTheory.ProjSpace.toProj f (t σ m) (ht σ m)) → ∃ hx' : (a' ≫ g) ≫ π = (a ≫ g) ≫ π, ∀ σ (i : ℕ), F.step (a' ≫ g) hx' σ i = F.step (a ≫ g) rfl σ i := by
  first | exact @GlobalTheory.FlagPlucker.Sep.step_eq_of_toProj_eq | exact GlobalTheory.FlagPlucker.Sep.step_eq_of_toProj_eq | (intros; apply GlobalTheory.FlagPlucker.Sep.step_eq_of_toProj_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieHaarLeTwoMulTangentNormalizedHaarStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieHaar_le_two_mul_tangentNormalizedHaar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (lam : Measure (realLie Ψ G)) [lam.IsAddHaarMeasure], ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set (realLie Ψ G), MeasurableSet s → s ⊆ Metric.ball 0 δ → lam s ≤ 2 * tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := by
  first | exact @GlobalTheory.CovTop.VolUp.LowDens.lam_le_two_mul_tangentHaar | exact GlobalTheory.CovTop.VolUp.LowDens.lam_le_two_mul_tangentHaar | (intros; apply GlobalTheory.CovTop.VolUp.LowDens.lam_le_two_mul_tangentHaar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftToLocalRingOpenImmersion
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

theorem GlobalTheory.openImmersion_factor_localization_atPrime : ∀ {X U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] {A : Type} [CommRing A] (ξ : Sp A ⟶ X)
    (𝔭 : PrimeSpectrum A), ξ 𝔭 ∈ Set.range j →
    ∃ y : Sp (Localization.AtPrime 𝔭.asIdeal) ⟶ U, y ≫ j = spMap (algebraMap A _) ≫ ξ := by
  intro X U j _ A _ ξ 𝔭 h𝔭
  have hopen : IsOpen (Set.range j) := j.isOpenEmbedding.isOpen_range
  have hsub : Set.range (spMap (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) ≫ ξ) ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    have hx : x ⤳ IsLocalRing.closedPoint (Localization.AtPrime 𝔭.asIdeal) :=
      IsLocalRing.specializes_closedPoint x
    have h2 := hx.map (spMap (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) ≫ ξ).continuous
    refine h2.mem_open hopen ?_
    have hc : (spMap (algebraMap A (Localization.AtPrime 𝔭.asIdeal))) (IsLocalRing.closedPoint (Localization.AtPrime 𝔭.asIdeal)) = 𝔭 := by
      apply PrimeSpectrum.ext
      exact Localization.AtPrime.under_maximalIdeal
    change ξ ((spMap (algebraMap A (Localization.AtPrime 𝔭.asIdeal))) (IsLocalRing.closedPoint (Localization.AtPrime 𝔭.asIdeal))) ∈ _
    rw [hc]; exact h𝔭
  exact ⟨IsOpenImmersion.lift j _ hsub, IsOpenImmersion.lift_fac _ _ _⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOfGeneratorFpqcDescent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

namespace GlobalTheory.FlatDescent

theorem injective_app_of_flat {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    (U : X.Opens) : Function.Injective (p.app U) := by
  have := effectiveEpi_morphismRestrict p U
  intro a b hab
  have hb : Function.Bijective U.topIso.inv := ConcreteCategory.bijective_of_isIso _
  apply hb.1
  apply injective_appTop_of_epi (p ∣_ U)
  rw [appTop_morphismRestrict_apply, appTop_morphismRestrict_apply, hab]

theorem unit_ext_of_flat {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    {U : X.Opens} {a b : Γ(X, U)ˣ} (h : ∀ y : Y, p y ∈ U → gm p y U a = gm p y U b) : a = b := by
  have e : pullU p U a = pullU p U b := unit_ext fun y hy => by
    rw [gm_pull (𝟙 Y) p y U hy, gm_pull (𝟙 Y) p y U hy, Category.id_comp]
    exact h y hy
  exact Units.ext (injective_app_of_flat p U (congrArg Units.val e))

theorem exists_unit_of_gm_eq {X X' Z : Scheme.{0}} (f : X' ⟶ X) [Flat f] [Surjective f] [QuasiCompact f]
    {g₁ g₂ : Z ⟶ X'} (h : IsPullback g₁ g₂ f f) (U : X.Opens) (s : Γ(X', f ⁻¹ᵁ U)ˣ)
    (hs : ∀ z : Z, f (g₁ z) ∈ U → gm g₁ z _ s = gm g₂ z _ s) :
    ∃ a : Γ(X, U)ˣ, pullU f U a = s := by
  have hg : g₁ ⁻¹ᵁ f ⁻¹ᵁ U ≤ g₂ ⁻¹ᵁ f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h.w]
  have e : res le_rfl (pullU g₁ _ s) = res hg (pullU g₂ _ s) := unit_ext fun z hz => by
    rw [gm_res _ z _ hz, gm_res _ z _ hz, gm_pull (𝟙 Z) g₁ z _ hz, gm_pull (𝟙 Z) g₂ z _ (hg hz),
      Category.id_comp, Category.id_comp]
    exact hs z hz
  obtain ⟨a, ha, -⟩ := (existsUnique_app_eq_iff f h U _ rfl le_rfl hg s.val).2 (congrArg Units.val e)
  obtain ⟨a, rfl⟩ := (isUnit_app_iff f U a).1 (ha ▸ s.isUnit)
  exact ⟨a, Units.ext ha⟩

theorem triv_of_gen_descent : ∀ {X X' Z : Scheme.{0}} (M : LB X), M.IsLB → ∀ (f : X' ⟶ X), Flat f →
    Surjective f → QuasiCompact f → ∀ (g₁ g₂ : Z ⟶ X'), IsPullback g₁ g₂ f f →
    ∀ t : LB.Gen (M.pull f), t.IsGen →
    (∀ (z : Z) (J : (Z ⟶ X) → M.ι), Geo.Tor.Good M z J → val t g₁ z J = val t g₂ z J) → Triv M := by
  intro X X' Z M hM f _ _ _ g₁ g₂ h t ht hv
  have le : ∀ i, f ⁻¹ᵁ M.U i ≤ LB.wchart M (fun _ : PUnit => f) (fun _ => i) := fun i x hx =>
    Set.mem_iInter.2 fun _ => hx
  have ex : ∀ i, ∃ a : Γ(X, M.U i)ˣ, pullU f _ a = res (le i) (t.s fun _ => i) := fun i =>
    exists_unit_of_gm_eq f h (M.U i) _ fun z hz => by
      have hz₂ : f (g₂ z) ∈ M.U i := (congrArg (fun q : Z ⟶ X => q z ∈ M.U i) h.w).mp hz
      obtain ⟨J, hJ, eJ⟩ := exists_good M hM z (fun _ : PUnit => g₁ ≫ f) (fun _ => i)
        (fun _ _ _ => rfl) (fun _ => hz)
      have v := hv z J hJ
      rw [val_of t g₁ z J (fun _ => i) eJ,
        val_of t g₂ z J (fun _ => i) (fun k => h.w ▸ eJ k)] at v
      exact (gm_res g₁ z _ hz _).trans (v.trans (gm_res g₂ z _ hz₂ _).symm)
  choose a ha using ex
  have ga : ∀ i (y : X'), f y ∈ M.U i →
      gm f y (M.U i) (a i) = gm (𝟙 X') y (LB.wchart M (fun _ : PUnit => f) (fun _ => i)) (t.s fun _ => i) :=
    fun i y hy => by
      have := gm_pull (𝟙 X') f y (M.U i) hy (a i)
      rw [Category.id_comp, ha] at this
      exact this.symm.trans (gm_res (𝟙 X') y (le i) hy _)
  refine ⟨⟨a⟩, fun i j => unit_ext_of_flat f fun y hy => ?_⟩
  have c := gen_trans ht (𝟙 X') y (j := fun _ => i) (j' := fun _ => j) (le i hy.1) (le j hy.2)
  rw [← ga i y hy.1, ← ga j y hy.2, trF, Fintype.prod_unique, zpow_one, Category.id_comp] at c
  exact (gm_res f y _ hy _).trans (c.trans ((map_mul _ _ _).trans (congrArg _ (gm_res f y _ hy _))).symm)

end GlobalTheory.FlatDescent
end

