import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0020
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0025
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceLocalizationExists
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0017
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0021
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsIntegrallyClosedOfDenomBis
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatTest

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsDualFamily
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem smul_mem_spanOver {o C V : Type} [CommRing o] [Field C] [Algebra o C] [AddCommGroup V] [Module C V]
    (RC : Subalgebra o C) (S : Set V) {a : C} (ha : a ∈ RC) {x : V} (hx : x ∈ spanOver RC S) :
    a • x ∈ spanOver RC S := by
  refine AddSubgroup.closure_induction (fun x hx => ?_) ?_ (fun x y _ _ h1 h2 => ?_) (fun x _ h => ?_) hx
  · obtain ⟨b, hb, e, he, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * b, RC.mul_mem ha hb, e, he, smul_smul a b e⟩
  · rw [smul_zero]; exact AddSubgroup.zero_mem _
  · rw [smul_add]; exact AddSubgroup.add_mem _ h1 h2
  · rw [smul_neg]; exact AddSubgroup.neg_mem _ h

theorem exists_dual_family (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] :
    ∃ (n : ℕ) (e : Fin n → M) (f : Fin n → Module.Dual A M), ∀ m, ∑ i, f i m • e i = m := by
  obtain ⟨n, t, ht⟩ := Module.Finite.exists_fin' A M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property t LinearMap.id ht
  refine ⟨n, fun i => t (Pi.single i 1), fun i => LinearMap.proj i ∘ₗ s, fun m => ?_⟩
  have h := LinearMap.congr_fun hs m
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h
  conv_rhs => rw [← h, pi_eq_sum_univ' (s m), map_sum]
  simp only [map_smul, LinearMap.comp_apply, LinearMap.proj_apply]

theorem lattices_alg {O Ω C : Type} [CommRing O] [Field Ω] [Field C] [Algebra O Ω] [Algebra O C] [Algebra Ω C]
    (R : Subalgebra O Ω) (RC : Subalgebra O C) (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC)
    {L Li : Type} [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L]
    [AddCommGroup Li] [Module Ω Li] (toLi : L →ₗ[R] Li) (hbc : IsBaseChange Ω toLi)
    (j : Module.Dual R L →ₗ[R] Module.Dual Ω Li) (hj : ∀ u v, j u (toLi v) = algebraMap R Ω (u v))
    (om : Submodule R (Module.Dual Ω Li)) (hom : om = LinearMap.range j) {g : ℕ}
    (io : om →ₛₗ[toRC R RC hR] (Fin g → RC)) (ev : Li → ((Fin g → C) →ₗ[C] C))
    (hio : Submodule.span RC (Set.range io) = ⊤)
    (hev : ∀ v (u : om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    {r : ℕ} (b : Fin r → Li) (co : Li →ₗ[Ω] (Fin r → Ω)) (hco : ∀ k, co (b k) = Pi.single k 1)
    (W : AddSubgroup (Fin r → Ω)) (hW1 : ∀ v, co (toLi v) ∈ W)
    (hW2 : ∀ a ∈ W, ∀ u ∈ om, u (∑ k, a k • b k) ∈ R) :
    (∀ z : Fin r → C, z ∈ spanOver RC (bcMap Ω C _ '' dotDual R W) ↔
        ∃ u : Fin g → RC, ∀ k, z k = ev (b k) fun j => (u j : C)) ∧
    ∀ a : Fin r → C, a ∈ spanOver RC (bcMap Ω C _ '' W) ↔
      ∀ u : Fin g → RC, ∑ k, a k * ev (b k) (fun j => (u j : C)) ∈ RC := by
  classical
  have hadd : ∀ x (u u' : Fin g → RC), ev x (fun j => ((u + u') j : C)) =
      ev x (fun j => (u j : C)) + ev x fun j => (u' j : C) := fun x u u' => by
    rw [← map_add]; rfl
  have hsm : ∀ x (s : RC) (u : Fin g → RC), ev x (fun j => ((s • u) j : C)) =
      (s : C) * ev x (fun j => (u j : C)) := fun x s u => by
    rw [← smul_eq_mul, ← map_smul]; rfl
  have hzero : ∀ x, ev x (fun j => ((0 : Fin g → RC) j : C)) = 0 := fun x => map_zero (ev x)
  have hall : ∀ u : Fin g → RC, u ∈ Submodule.span RC (Set.range io) := fun u => by rw [hio]; trivial
  have hdd : ∀ m, m ∈ dotDual R W ↔ ∀ l ∈ W, l ⬝ᵥ m ∈ R := fun m => by
    simp only [dotDual, AddSubgroup.mem_iInf]
    rfl
  refine ⟨fun z => ⟨fun hz => ?_, ?_⟩, fun a => ⟨fun ha u => ?_, fun ha => ?_⟩⟩
  · refine AddSubgroup.closure_induction (p := fun z _ => ∃ u : Fin g → RC, ∀ k, z k = ev (b k) fun j => (u j : C))
      ?_ ⟨0, fun k => (hzero _).symm⟩ ?_ ?_ hz
    · rintro _ ⟨s, hs, _, ⟨m, hm, rfl⟩, rfl⟩
      let U : Module.Dual Ω Li := (Fintype.linearCombination Ω m) ∘ₗ co
      have hU : ∀ x, U x = co x ⬝ᵥ m := fun x => by
        simp [U, Fintype.linearCombination_apply, dotProduct]
      let w₀ : Module.Dual R L :=
        { toFun := fun v => ⟨U (toLi v), by rw [hU]; exact (hdd m).1 hm _ (hW1 v)⟩
          map_add' := fun a b => Subtype.ext (by simp)
          map_smul' := fun a b => Subtype.ext (by
            change U (toLi (a • b)) = (a : Ω) * U (toLi b)
            rw [toLi.map_smul, ← smul_eq_mul, ← U.map_smul]; rfl) }
      have hjw : j w₀ = U := hbc.algHom_ext _ _ fun v => by rw [hj]; rfl
      refine ⟨(⟨s, hs⟩ : RC) • io ⟨U, by rw [hom]; exact ⟨w₀, hjw⟩⟩, fun k => ?_⟩
      rw [hsm, hev]
      change s * algebraMap Ω C (m k) = s * algebraMap Ω C (U (b k))
      rw [hU, hco, single_one_dotProduct]
    · rintro x y _ _ ⟨u, hu⟩ ⟨u', hu'⟩
      exact ⟨u + u', fun k => by rw [hadd, ← hu, ← hu']; rfl⟩
    · rintro x _ ⟨u, hu⟩
      exact ⟨(-1 : RC) • u, fun k => by rw [hsm, ← hu]; simp⟩
  · rintro ⟨u, hu⟩
    obtain rfl : z = fun k => ev (b k) fun j => (u j : C) := funext hu
    clear hu
    induction hall u using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨y, rfl⟩ := h
      refine AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨fun k => y.1 (b k), (hdd _).2 fun l hl => ?_, rfl⟩, ?_⟩
      · have := hW2 l hl y.1 y.2
        rw [map_sum] at this
        simpa only [map_smul, smul_eq_mul, dotProduct] using this
      · rw [one_smul]
        exact funext fun k => hev _ _
    | zero => simp only [hzero]; exact AddSubgroup.zero_mem _
    | add x y _ _ hx hy => simp only [hadd]; exact AddSubgroup.add_mem _ hx hy
    | smul s x _ hx => simp only [hsm]; exact smul_mem_spanOver RC _ s.2 hx
  · refine AddSubgroup.closure_induction (p := fun a _ => ∑ k, a k * ev (b k) (fun j => (u j : C)) ∈ RC)
      ?_ (by simp) ?_ ?_ ha
    · rintro _ ⟨s, hs, _, ⟨a₀, ha₀, rfl⟩, rfl⟩
      have key : ∑ k, algebraMap Ω C (a₀ k) * ev (b k) (fun j => (u j : C)) ∈ RC := by
        refine Submodule.span_induction
          (p := fun u _ => ∑ k, algebraMap Ω C (a₀ k) * ev (b k) (fun j => ((u : Fin g → RC) j : C)) ∈ RC)
          ?_ ?_ ?_ ?_ (hall u)
        · rintro _ ⟨y, rfl⟩
          have := hR _ (hW2 a₀ ha₀ y.1 y.2)
          rw [map_sum, map_sum] at this
          simpa only [map_smul, smul_eq_mul, map_mul, hev] using this
        · simp only [hzero, mul_zero, Finset.sum_const_zero]; exact RC.zero_mem
        · intro x y _ _ hx hy
          simp only [hadd, mul_add, Finset.sum_add_distrib]
          exact RC.add_mem hx hy
        · intro s x _ hx
          simp only [hsm, mul_left_comm _ (s : C), ← Finset.mul_sum]
          exact RC.mul_mem s.2 hx
      have := RC.mul_mem hs key
      rw [Finset.mul_sum] at this
      convert this using 2 with k
      exact _root_.mul_assoc _ _ _
    · intro x y _ _ hx hy
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      exact RC.add_mem hx hy
    · intro x _ hx
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
      exact RC.neg_mem hx
  · obtain ⟨n, e, f, hef⟩ := exists_dual_family R L
    have hid : (∑ m, (j (f m)).smulRight (toLi (e m)) : Li →ₗ[Ω] Li) = LinearMap.id :=
      hbc.algHom_ext _ _ fun v => by
        rw [LinearMap.id_apply, LinearMap.sum_apply]
        conv_rhs => rw [← hef v, map_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [LinearMap.smulRight_apply, hj, map_smul, algebraMap_smul]
    have hk : ∀ k k', (Pi.single k 1 : Fin r → Ω) k' = ∑ m, j (f m) (b k) * co (toLi (e m)) k' := fun k k' => by
      have := congrArg co (LinearMap.congr_fun hid (b k))
      rw [LinearMap.id_apply, hco, LinearMap.sum_apply, map_sum] at this
      rw [← this, Finset.sum_apply]
      simp only [LinearMap.smulRight_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    have hjm : ∀ m, j (f m) ∈ om := fun m => by rw [hom]; exact ⟨_, rfl⟩
    have ha' : a = ∑ m, (∑ k, a k * ev (b k) (fun i => (io ⟨_, hjm m⟩ i : C))) • bcMap Ω C _ (co (toLi (e m))) := by
      funext k'
      rw [Finset.sum_apply]
      simp only [hev, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      have : ∀ k, ∑ m, a k * algebraMap Ω C (j (f m) (b k)) * bcMap Ω C _ (co (toLi (e m))) k' =
          a k * algebraMap Ω C ((Pi.single k 1 : Fin r → Ω) k') := fun k => by
        rw [hk, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_mul, _root_.mul_assoc]
        rfl
      simp only [this]
      rw [Finset.sum_eq_single k' (fun k _ h => by simp [Pi.single_eq_of_ne h.symm]) (by simp)]
      simp
    rw [ha']
    exact AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure ⟨_, ha _, _, ⟨_, hW1 _, rfl⟩, rfl⟩

theorem lattices (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ) (hd : IsArithVar (mCoordIdeal y) (d + 1)) (hpq : 0 < D.p + D.q) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime] (hpm : (p : A) ∈ m) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k) (hc' : mseg y c' ≠ 0) (P : ChartPack G O c') (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C)
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr E) (hR : ∀ a ∈ CR O y c', algebraMap Ω C a ∈ RC) {g : ℕ}
    (io : P.Dh.om →ₛₗ[toRC (CR O y c') RC hR] (Fin g → RC)) (ev : 𝔐.Li → ((Fin g → C) →ₗ[C] C))
    (hio : Submodule.span RC (Set.range io) = ⊤)
    (hev : ∀ v (u : P.Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    (t : CMType H ⊕ CMType H) {r : ℕ} (b : Fin r → 𝔐.Li) (hb : LinearIndependent Ω b)
    (hb' : Submodule.span Ω (Set.range b) = 𝔐.Vgen t) :
    (∀ z : Fin r → C,
      z ∈ spanOver RC (bcMap Ω C _ '' dotDual (CR O y c') (coordLat O y (𝔐.dR t) b c')) ↔
        ∃ u : Fin g → RC, ∀ k, z k = ev (b k) fun j => (u j : C)) ∧
    ∀ a : Fin r → C, a ∈ spanOver RC (bcMap Ω C _ '' coordLat O y (𝔐.dR t) b c') ↔
      ∀ u : Fin g → RC, ∑ k, a k * ev (b k) (fun j => (u j : C)) ∈ RC := by
  classical
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  haveI := 𝔐.t.semi.smooth
  haveI := 𝔐.t.semi.comm
  haveI := P.fin
  haveI := P.proj
  have hinj : Function.Injective (algebraMap (CR O y c') Ω) := Subtype.val_injective
  obtain ⟨σ, hσ, -, -⟩ := PositivityTheory.Xgn.exists_cm_type_embedding E H D l Xo c O₀ β Y S Ω K J y 𝔐 t
  obtain ⟨hσO, x₀, hx₀, o₀, ho₀⟩ :=
    PositivityTheory.Xgn.SequenceDifferentials.main E Ω p hdisc A m hpm O σ
  have hσR : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap (CR O y c') Ω).range := fun a => by
    obtain ⟨o, ho⟩ := hσO a
    exact ⟨algebraMap O _ o, ho⟩
  have hdual : ∀ k, σ (HT.dualInt E k) ∈ (algebraMap (CR O y c') Ω).range := fun k => by
    have := (HT.different_generator_dualInt (CR O y c') Ω E σ 1 hinj hσR (le_antisymm ?_ ?_)).2.1 k
    · rwa [map_one, _root_.one_mul] at this
    · rw [Submodule.span_singleton_le_iff_mem, map_one, ← ho₀]
      exact Submodule.smul_mem _ (algebraMap O (CR O y c') o₀) (Submodule.subset_span ⟨x₀, hx₀, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨x, -, rfl⟩
      obtain ⟨s, hs⟩ := hσR x
      exact Submodule.mem_span_singleton.2 ⟨s, by rw [map_one, Algebra.smul_def, _root_.mul_one, hs]⟩
  have heig : ∀ x, x ∈ HT.eigSp 𝔐.ρ σ ↔ x ∈ 𝔐.Vgen t := fun x => by
    rw [HT.LatBasic.mem_eigSp]
    simp [HodgeCpt.Vgen, GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, sub_eq_zero, hσ]
  have hπ : ∀ x, HT.eigProj 𝔐.ρ σ x ∈ Submodule.span Ω (Set.range b) := fun x => by
    rw [hb', ← heig]
    exact HT.LatBasic.eigProj_mem _ _ _
  let co : 𝔐.Li →ₗ[Ω] (Fin r → Ω) := (Finsupp.linearEquivFunOnFinite Ω Ω (Fin r)).toLinearMap ∘ₗ hb.repr ∘ₗ
    (HT.eigProj 𝔐.ρ σ).codRestrict _ hπ
  have hsum : ∀ x, ∑ k, co x k • b k = HT.eigProj 𝔐.ρ σ x := fun x => by
    have := hb.linearCombination_repr ⟨_, hπ x⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    exact this
  have hco : ∀ k, co (b k) = Pi.single k 1 := fun k => by
    have h1 : HT.eigProj 𝔐.ρ σ (b k) = b k :=
      HT.LatBasic.eigProj_of_mem ((heig _).2 (hb' ▸ Submodule.subset_span ⟨k, rfl⟩))
    refine funext (Fintype.linearIndependent_iffₛ.1 hb _ _ ?_)
    rw [hsum, h1, Finset.sum_eq_single k (fun i _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]
    simp
  have hρ : ∀ a v, 𝔐.ρ a (P.toLi v) = P.toLi (P.ρ a v) := fun a v => by
    apply 𝔐.M.inj
    apply Over.OverMorphism.ext
    rw [𝔐.act a (P.toLi v), P.toLi_pt, P.act a v, Over.comp_left, P.toLi_pt, Over.comp_left, Category.assoc]
  refine lattices_alg (CR O y c') RC hR P.toLi P.toLi_bc P.j P.j_apply P.Dh.om P.isHT.1 io ev hio hev b co hco _
    (fun v => ?_) fun a ha u hu => ?_
  · rw [Fam.mem_coordLat_iff]
    intro q hq hO
    have hsub : ∀ a : CR O y c', algebraMap (CR O y c') Ω a ∈ regAt 𝔐.ξ q := fun a =>
      GlobalTheory.CompanionTheory.Ar.Fam.chartRing_le_regAt O y c' q hq hO a.2
    have hr : q.1 ∈ Set.range P.x := by
      obtain ⟨U, hU, hmem⟩ := 𝔐.tie.affine c' hc'
      exact PositivityTheory.Xgn.SequenceLocalization.mem_range hξ hU _ P.x P.x_gen (fun z => (hmem _).2 ⟨𝔐.all _,
        (PositivityTheory.Xgn.exists_function_at_point E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O G c' hc' P z).1⟩)
        q ((hmem _).2 ⟨q.2, hq⟩) hsub
    obtain ⟨Q, hQ⟩ : ∃ Q : PrimeSpectrum (CR O y c'), P.x Q = q.1 := hr
    obtain ⟨_, -, hzs, hg⟩ := GlobalTheory.CompanionTheory.HtLink.stalk_loc hξ _ hinj P.x P.x_gen Q q hQ hsub
    have hlat : ∀ v, P.toLi v ∈ 𝔐.M.lat q := fun v =>
      Submodule.subset_span (GlobalTheory.CompanionTheory.HtLink.tan_ext 𝔐.M P.M hzs (genMap 𝔐.ξ q) hg P.toLi P.toLi_pt v)
    rw [hsum]
    refine ⟨?_, (heig _).1 (HT.LatBasic.eigProj_mem _ _ _)⟩
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, hρ]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨s, hs⟩ := hdual k
    exact (𝔐.M.lat q).smul_mem ⟨_, hs ▸ hsub s⟩ (hlat _)
  · exact PositivityTheory.Xgn.sequence_family_pairing E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p hpS A m hpm O G c' hc' P
      u hu _ fun q h1 h2 => ((Fam.mem_coordLat_iff O y _ b c' a).1 ha q h1 h2).1

end PositivityTheory.Xgn.TestGroupPoint
end
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ReducesAtOfWithE
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

open GlobalTheory.CompanionTheory.Ar.HT PositivityTheory.Xgn.TestGroupPoint.Par

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]

def ReducesAt (D : HTChart A K c p R N Ω) (κ : A) (C O : Type) [Field C] [CommRing O] [Algebra O C] [Algebra A O] :
    Prop :=
  ∃ (V Ω' : Type) (_ : AddCommGroup V) (_ : Module C V) (_ : Module O V) (_ : IsScalarTower O C V)
    (_ : AddCommGroup Ω') (_ : Module C Ω') (_ : Module O Ω') (_ : IsScalarTower O C Ω')
    (P : HTPoint C O c (algebraMap A O κ) N V Ω') (io : D.om →ₛₗ[algebraMap A O] Ω'),
    D.ReducesTo (algebraMap A O) P io

theorem reducesAt_of_withE [NeZero (p ^ R)] (D : HTChart A K c p R N Ω)
    (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)) (alt adj hs hi) (a : ℕ) (ha : a.Coprime p)
    (he : ∀ x y, D.e x y = (a : ZMod (p ^ R)) * e x y) (κ : A) {C O : Type} [Field C] [CommRing O] [Algebra O C]
    [Algebra A O] {v : Valuation C NNReal} (hv : v.Integers O) (hp : v (p : C) < 1)
    (h : ReducesAt (withE D e alt adj hs hi) κ C O) : ReducesAt D κ C O := by
  obtain ⟨V, Ω', j1, j2, j3, j4, j5, j6, j7, j8, P, io, hr⟩ := h
  obtain ⟨b, hb⟩ := isUnit_of_coprime hv (by rwa [map_natCast]) ha
  refine ⟨V, Ω', j1, j2, j3, j4, j5, j6, j7, j8, scalePt P b, io,
    ⟨hr.span_eq, hr.rank_eq, hr.lin, hr.ht_eq, fun x y => ?_⟩⟩
  obtain ⟨z, hz⟩ := hr.e_eq x y
  have h1 : ((D.e x y).val : O) + (p : O) ^ R * ((a * (e x y).val / p ^ R : ℕ) : O) = (a : O) * ((e x y).val : O) := by
    have h0 : (D.e x y).val = (a * (e x y).val) % p ^ R := by
      rw [he, ← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [h0]
    exact_mod_cast congrArg (Nat.cast : ℕ → O) (Nat.mod_add_div (a * (e x y).val) (p ^ R))
  refine ⟨((a * (e x y).val / p ^ R : ℕ) : O) + a * z, ?_⟩
  change algebraMap O C (b : O) • P.e (P.tate x) (P.tate y) = _
  rw [hz, smul_eq_mul, ← map_mul, hb]
  congr 1
  change (a : O) * (((e x y).val : O) + (p : O) ^ R * z) = _
  linear_combination -h1

end Chart

open TensorProduct in
theorem reducesAt_of : PointHT → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω] (Dc : HTChart R K (IsCMField.complexConj E).toRingEquiv p n (D.p + D.q) Ω) (u : Fin (D.p + D.q) → D.La) (hu : IsPolLattice (IsCMField.complexConj E).toRingEquiv p D.EF u) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (x : Sp R ⟶ S) (Γ₀ : QFGroup R (LevGrp D.La p n)) (i : Γ₀.G.left ⟶ t.G.left) (hi : Γ₀.IsTorsionAlong t.G x (p ^ n) i) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel t.G x L) (ρ : 𝓞 E →+* Module.End R L) (hρ : M.IsActOf t.act.act ρ) (j : Module.Dual R L →ₗ[R] Ω) (hj : IsBaseChange K j) (π : Multiplicative (Fin (D.p + D.q) → 𝓞 E) →* LevGrp D.La p n) (ζ₀ : Rˣ) (κ : R), IsHTChartOf Dc Γ₀ i M ρ j π ζ₀ → (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) → (∀ z z', Dc.e z z' = ((D.EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) → 2 * Module.finrank R L = Module.finrank ℤ D.La → IsProper (Limits.pullback.snd t.G.hom ((BT.genPt R).hom ≫ x)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (f : FractionRing R →+* k), ∃ I : TateIso D k (Over.mk (spMap f ≫ (BT.genPt R).hom ≫ x) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (I.ζ (p ^ n) : k) = f (algebraMap R _ (ζ₀ : R)) ∧ ∀ a, (I.ev (p ^ n) a).left = spMap f ≫ (Γ₀.pt (lev p n a)).left ≫ i) → (if p = 2 then κ = 4 else ∃ ζ : R, IsPrimitiveRoot ζ p ∧ κ = ζ - 1) → ∀ (C O : Type) [Field C] [IsAlgClosed C] [CharZero C] [CommRing O] [IsDomain O] [Algebra O C] [Algebra R O] (v : Valuation C NNReal), v.Integers O → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : O)}) O → Function.Injective (algebraMap R O) → ReducesAt Dc κ C O := by
  intro hPt E _ _ _ H D p _ R K _ _ _ _ _ _ _ _ n Ω _ _ _ _ Dc u hu S _ t x Γ₀ i hi L _ _ M ρ hρ j hj π ζ₀ κ hc hπ he hrank hprop hTate hκ C O _ _ _ _ _ _ _ v hv hp hO hinj
  obtain ⟨-, -, hIC, -, hAC, -⟩ := PositivityTheory.HtPt.Twhopf.padic_alg p C v O hv hp hO
  haveI := hAC
  haveI := hIC
  have hgk : Function.Injective ((algebraMap O (FractionRing O)).comp (algebraMap R O)) :=
    (IsFractionRing.injective O _).comp hinj
  let f : FractionRing R →+* FractionRing O := IsFractionRing.lift hgk
  have hf : ∀ r, f (algebraMap R _ r) = algebraMap O _ (algebraMap R O r) :=
    fun r => IsFractionRing.lift_algebraMap hgk r
  obtain ⟨I, hI1, hI2⟩ := hTate (FractionRing O) f
  have hz : spMap f ≫ (BT.genPt R).hom ≫ x = (BT.genPt O).hom ≫ spMap (algebraMap R O) ≫ x := by
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    simp only [Over.mk_hom, spMap]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hf
  obtain ⟨L', iA', iM', P, io, hio⟩ := PositivityTheory.HtPt.Htat.TestPts.reduces_at_point hPt E H D p R K n Ω Dc u hu S t x Γ₀
    i hi L M ρ hρ j hj π ζ₀ κ hc hπ he hrank hprop hκ C O v hv hp hO hinj f hf _ hz I hI1 hI2
  exact ⟨C ⊗[ℤ] D.La, C ⊗[O] Module.Dual O L', inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, P, io, hio⟩

set_option maxHeartbeats 3200000 in
open PositivityTheory.HtPt.Htat in
theorem reducesAt_pack (hF : HT.FarguesHodgeTate) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ) (hd : IsArithVar (mCoordIdeal y) (d + 1)) (hpq : 0 < D.p + D.q) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime] (hpm : (p : A) ∈ m) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k) (hc' : mseg y c' ≠ 0) (P : ChartPack G O c')
    (w : O) (hw : HT.IsCp p (algebraMap O Ω w)) (C O' : Type) [Field C] [IsAlgClosed C] [CharZero C] [CommRing O']
    [IsDomain O'] [Algebra O' C] [Algebra (CR O y c') O'] (v : Valuation C NNReal) (hv : v.Integers O')
    (hvp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O')}) O')
    (hφ : Function.Injective (algebraMap (CR O y c') O')) :
    ReducesAt P.Dh (algebraMap O (CR O y c') w) C O' := by
  obtain ⟨h0, hNoe, hIC, hFr⟩ :=
    chart_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O c' hc'
  obtain ⟨-, hN, hprop, hTa, hrk, -, -⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS
    (zp Ω p) (mem_range_zp Ω p)
  have hp := (Fact.out : p.Prime)
  have hn : p ^ 𝔐.R p ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero (p ^ 𝔐.R p) := ⟨hn⟩
  have hR : 1 ≤ 𝔐.R p := le_trans (by norm_num) (𝔐.R_ge p hpS)
  have hinj : Function.Injective (algebraMap (CR O y c') Ω) := IsFractionRing.injective _ _
  haveI : CharZero (CR O y c') := (algebraMap (CR O y c') Ω).charZero
  obtain ⟨ev, ζ₀, hev⟩ := exists_isParam D 𝔐.t 𝔐.ξ GlobalTheory.T.torsion_points_defined_generic (p ^ 𝔐.R p) (Nat.pos_of_ne_zero hn) hpq hprop
    (𝔐.tors p hpS) hTa
  obtain ⟨u, hu, huz⟩ := exists_coords D 𝔐.t 𝔐.ξ p (𝔐.R p) hR hev G.t₂.pt G.t₂.onto G.t₂.lin
  obtain ⟨π, e, hπ, he, hdec, hsurj, hker, halt, hadj, hes, hei⟩ :=
    exists_levPairing (HT.cmConj E) p (𝔐.R p) D.EF u hu
  obtain ⟨b, hb⟩ := exists_mulEquiv π (qhom (D.p + D.q) (p ^ 𝔐.R p)) hsurj (qhom_surj _ _)
    (fun z => (hker z.toAdd).trans (qhom_eq_one _ _ z.toAdd).symm)
  have hζ₀ : IsPrimitiveRoot (ζ₀ : Ω) (p ^ 𝔐.R p) := IsPrimitiveRoot.coe_units_iff.2 hev.prim
  obtain ⟨a, -, hac, haζ⟩ := (G.ζ_prim.isPrimitiveRoot_iff).1 hζ₀
  have hap : a.Coprime p := Nat.Coprime.coprime_dvd_right (dvd_pow_self p (by omega)) hac
  have hee : ∀ x x', G.e x x' = (a : ZMod (p ^ 𝔐.R p)) * e x x' := by
    intro x x'
    let i : Ω →+* AlgebraicClosure Ω := algebraMap Ω _
    let ψ := bcPt 𝔐.ξ i _ rfl
    let cc : (AlgebraicClosure Ω)ˣ :=
      Units.map i.toMonoidHom (ζ₀ ^ D.EF (∑ k, x k • u k) (∑ k, x' k • u k))
    have h1 := (hev.weil (∑ k, x k • u k) (∑ k, x' k • u k) _ i (ψ ≫ ev _) (ψ ≫ ev _) cc rfl rfl).2 rfl
    have h2 := (G.weil x x' _ i _ _ cc (by rw [← huz]; rfl) (by rw [← huz]; rfl)).1 h1
    have h3 : ((ζ₀ ^ D.EF (∑ k, x k • u k) (∑ k, x' k • u k) : Ωˣ) : Ω) = G.ζ ^ (G.e x x').val := i.injective h2
    rw [← pow_val_intCast ζ₀ _ hev.prim.pow_eq_one, ← he, Units.val_pow_eq_pow_val, ← haζ,
      ← pow_val_mul _ _ G.ζ_prim.pow_eq_one] at h3
    exact ZMod.val_injective _ (G.ζ_prim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3.symm)
  refine reducesAt_of_withE P.Dh e halt hadj hes hei a hap (fun x x' => by rw [P.Dh_e, hee]) _ hv hvp ?_
  have hζ1 : P.ζ ^ (p ^ 𝔐.R p) = 1 := Units.ext (hinj (by
    rw [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one]
    exact (congrArg (· ^ (p ^ 𝔐.R p)) P.ζ_eq).trans G.ζ_prim.pow_eq_one))
  have hζa : algebraMap (CR O y c') Ω ((P.ζ ^ a : (CR O y c')ˣ) : CR O y c') = ζ₀ := by
    rw [Units.val_pow_eq_pow_val, map_pow, ← haζ]
    exact congrArg (· ^ a) P.ζ_eq
  let κ : FractionRing (CR O y c') ≃+* Ω := (FractionRing.algEquiv (CR O y c') Ω).toRingEquiv
  have hκ : ∀ r, κ (algebraMap (CR O y c') _ r) = algebraMap (CR O y c') Ω r :=
    (FractionRing.algEquiv (CR O y c') Ω).commutes
  have hκf : fracToField (CR O y c') = κ.toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (CR O y c'))
    ext r
    exact (IsFractionRing.lift_algebraMap (g := algebraMap (CR O y c') Ω) hinj r).trans (hκ r).symm
  have hq : spMap κ.symm.toRingHom ≫ 𝔐.ξ = (BT.genPt (CR O y c')).hom ≫ P.x := by
    rw [← P.x_gen, ← Category.assoc, ← HTTie.spec_comp]
    congr 3
    ext r
    exact (RingEquiv.symm_apply_eq κ).2 (hκ r).symm
  haveI := P.fin
  refine reducesAt_of (GlobalTheory.T.pointHT_of_fargues_hodge_tate hF) E H D p (CR O y c') Ω (𝔐.R p) _ (withE P.Dh e halt hadj hes hei) u hu 𝔐.X 𝔐.t P.x (relabel P.Γ₂ b) P.i₂
    ⟨P.tors₂.isOver, P.tors₂.mul, P.tors₂.inj, P.tors₂.kernel⟩ P.L P.M P.ρ P.act P.j P.j_bc π (P.ζ ^ a) (algebraMap O (CR O y c') w)
    ⟨P.isHT.1, P.isHT.2.1, fun z => ?_⟩ hπ he ?_ (isProper_of_iso _ 𝔐.ξ _ _ hq) (fun k _ _ f => ?_)
    (cp_descend hinj p (algebraMap O (CR O y c') w) hw) C O' v hv hvp hO hφ
  · obtain ⟨χ, w₀, hχ, hh, s, hs, hHT⟩ := P.isHT.2.2 z
    refine ⟨χ.comp b.toMonoidHom, w₀, fun z' => ?_, hh, s, fun t => hs (b t), hHT⟩
    change χ (b (π _)) = (P.ζ ^ a) ^ (e z z').val
    rw [hb, hχ, P.Dh_e, hee, pow_val_mul _ _ hζ1]
  · rw [← hrk, P.toLi_bc.finrank_eq]
  · have hk : spMap (f.comp κ.symm.toRingHom) ≫ 𝔐.ξ = spMap f ≫ (BT.genPt (CR O y c')).hom ≫ P.x := by
      rw [← hq, Tor.spMap_comp, Category.assoc]
    obtain ⟨I, hz, hI⟩ := hev.tate' D 𝔐.t 𝔐.ξ k _ _ hk
    refine ⟨I, ?_, fun x => ?_⟩
    · rw [hz, ← hζa, ← hκ]
      exact congrArg f (κ.symm_apply_apply _)
    · obtain ⟨z, r, rfl⟩ := hdec x
      have e1 : HT.lev p (𝔐.R p) (∑ k, z k • u k + (p ^ 𝔐.R p) • r) = π (Multiplicative.ofAdd z) := by
        rw [hπ]
        refine congrArg Multiplicative.ofAdd ((Submodule.Quotient.eq _).2 ⟨r, ?_⟩)
        exact (add_sub_cancel_left _ _).symm
      rw [hI, hev.add, (hev.ker _).2 ⟨r, rfl⟩, _root_.mul_one, huz, P.pts₂, e1, hκf]
      change _ = spMap f ≫ (P.Γ₂.pt (b (π _))).left ≫ P.i₂
      rw [hb]
      exact spMap_cancel κ f _

theorem point_data (hF : HT.FarguesHodgeTate) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ) (hd : IsArithVar (mCoordIdeal y) (d + 1)) (hpq : 0 < D.p + D.q) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime] (hpm : (p : A) ∈ m) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k) (hc' : mseg y c' ≠ 0) (P : ChartPack G O c') (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C)
    (w : O) (hw : HT.IsCp p (algebraMap O Ω w)) (hT : IsTestPt p (CR O y c') RC) :
    ∃ (g : ℕ) (io : P.Dh.om →ₛₗ[toRC (CR O y c') RC hT.2.2.2] (Fin g → RC))
      (ev : 𝔐.Li → ((Fin g → C) →ₗ[C] C)) (Hm : Matrix (Fin g) (Ix E (D.p + D.q)) RC)
      (Eg : Matrix (Ix E (D.p + D.q)) (Ix E (D.p + D.q)) RC),
      Submodule.span RC (Set.range io) = ⊤ ∧
      (∀ v (u : P.Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v)) ∧
      Fintype.card (Ix E (D.p + D.q)) = g + g ∧ Egᵀ = -Eg ∧
      (∃ Ei : Matrix (Ix E (D.p + D.q)) (Ix E (D.p + D.q)) RC, Ei * Eg = 1 ∧ Hm * Ei * Hmᵀ = 0) ∧
      (∀ m m', Eg m m' - ((G.e (dl m) (dl m')).val : RC) ∈ Ideal.span {(p : RC)}) ∧
      ∀ m k, Hm k m - io ⟨P.Dh.h (dl m), P.Dh.h_mem _⟩ k ∈ Ideal.span {(p : RC)} := by
  obtain ⟨h0, hNoe, hIC, hFr⟩ := chart_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O c' hc'
  have hC := hT.1
  obtain ⟨v, hv, hvp⟩ := hT.2.1
  haveI : CharZero C := charZero_of_injective_ringHom (algebraMap Ω C).injective
  have hint : v.Integers RC :=
    ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun r hr => ⟨⟨r, (hv _).2 hr⟩, rfl⟩⟩
  letI : Algebra (CR O y c') RC := (toRC (CR O y c') RC hT.2.2.2).toAlgebra
  have hφ : Function.Injective (algebraMap (CR O y c') RC) := fun a b h =>
    Subtype.ext ((algebraMap Ω C).injective (congrArg Subtype.val h))
  obtain ⟨V, Ω', _, _, _, _, _, _, _, _, Pt, io₀, hr⟩ := reducesAt_pack hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p
    hpS A m hpm O G c' hc' P w hw C RC v hint hvp hT.2.2.1 hφ
  obtain ⟨g, io, Hm, Eg, h1, h2, h3, h4, h5, h6, h7⟩ :=
    chart_matrices (le_trans (by norm_num) (𝔐.R_ge p hpS)) P.Dh hint Pt io₀ hr
  let f : 𝔐.Li → (P.Dh.om →ₛₗ[algebraMap (CR O y c') RC] C) := fun x =>
    { toFun := fun u => algebraMap Ω C (u.1 x)
      map_add' := fun a b => by rw [Submodule.coe_add, LinearMap.add_apply, map_add]
      map_smul' := fun r a => by
        change algebraMap Ω C ((r : Ω) * a.1 x) = algebraMap Ω C (r : Ω) * algebraMap Ω C (a.1 x)
        rw [map_mul] }
  choose ev hev using fun x => h2 (f x)
  refine ⟨g, io, ev, Hm, Eg, h1, fun x u => hev x u, h3, h4, h5, fun m m' => ?_, h7⟩
  rw [← P.Dh_e]
  exact h6 m m'

end PositivityTheory.Xgn.TestGroupPoint
end
end

