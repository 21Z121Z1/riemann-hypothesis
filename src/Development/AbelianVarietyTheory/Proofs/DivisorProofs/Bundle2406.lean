import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2340
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0762
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0755
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomAtIffOfSpecializes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.LevelClopen

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem eSec_diag {A : Over S} [GrpObj A] :
    eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left = eSec A ≫ (lift (𝟙 A) (𝟙 A)).left := by
  simp only [eSec, ← Over.comp_left]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, Category.comp_id]
    rw [MonObj.comp_one]
    show toUnit _ ≫ η = η
    rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · simp

theorem exists_cub {b : Base D R} {s : S ⟶ Sp R} (o : Pre b s) :
    ∃ PP : RigLB o.A, PP.L = o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left ∧ Nonempty (CubicalStr o.A PP) := by
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  obtain ⟨t, ht⟩ := GlobalTheory.HkFam.cube_of_exists_relAmple o.ab hL o.ample hL
  have hR : Out.Rigidified o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) := by
    obtain ⟨t₁, ht₁⟩ := o.rig₁
    exact ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_pull_pull o.P (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left (eSec o.A) _
      (eSec o.A) eSec_diag ⟨pullGenLB t₁ (eSec o.A), pullGenLB_isGen ht₁ _⟩
  exact GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.abelianSchemeLaws_all.1 S o.A o.ab _ hL hR ⟨t, ht⟩

theorem isUnit_base {b : Base D R} {s : S ⟶ Sp R} (n : ℕ) (hnp : n.Coprime p) : IsUnit (n : Γ(S, ⊤)) := by
  have := ((b.unit n hnp).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map s.appTop.hom
  simpa using this

theorem geomAt_transport {b : Base D R} {N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {s : S ⟶ Sp R}
    (o : PreEta b N s) (R' : Type) [CommRing R'] [HenselianLocalRing R']
    [IsAlgClosed (IsLocalRing.ResidueField R')] (t : Sp R' ⟶ S) {k k' : Type} [Field k] [IsAlgClosed k]
    [Field k'] [IsAlgClosed k'] (i : Sp k ⟶ Sp R') (i' : Sp k' ⟶ Sp R') :
    o.GeomAt k (i ≫ t) → o.GeomAt k' (i' ≫ t) := by
  intro hT
  have hA := o.ab
  have hS : ∀ n : ℕ, 0 < n → n.Coprime p → IsUnit (n : Γ(S, ⊤)) :=
    fun n _ hnp => isUnit_base (b := b) (s := s) n hnp
  have hRu : ∀ n : ℕ, 0 < n → n.Coprime p → IsUnit (n : R') := by
    intro n hn hnp
    have := ((hS n hn hnp).map t.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom
    simpa using this
  obtain ⟨PP, hPP, ⟨cub⟩⟩ := exists_cub o.toPre
  unfold PreEta.GeomAt at hT ⊢
  change ∃ I : TateIsoO D k' (Over.mk (i' ≫ t) ⟶ o.A) _
      (fun n g g' z => Out.WeilIs o.A (o.toPre.P.pull (lift (𝟙 o.toPre.A) (𝟙 o.toPre.A)).left) n g g' (unitOn z)), _
  rw [← hPP]
  change ∃ I : TateIsoO D k (Over.mk (i ≫ t) ⟶ o.A) _
      (fun n g g' z => Out.WeilIs o.A (o.toPre.P.pull (lift (𝟙 o.toPre.A) (𝟙 o.toPre.A)).left) n g g' (unitOn z)), _ at hT
  rw [← hPP] at hT
  obtain ⟨φ, rfl⟩ : ∃ φ : R' →+* k, i = spMap φ := ⟨(Spec.preimage i).hom, by simp [spMap]⟩
  obtain ⟨φ', rfl⟩ : ∃ φ' : R' →+* k', i' = spMap φ' := ⟨(Spec.preimage i').hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := hT
  let A := o.A
  let lvR : D.La → (Over.mk t ⟶ A) := fun a => toUnit _ ≫ o.eta a
  let j : Over.mk (spMap φ ≫ t) ⟶ Over.mk t := Over.homMk (spMap φ) rfl
  let j' : Over.mk (spMap φ' ≫ t) ⟶ Over.mk t := Over.homMk (spMap φ') rfl
  have hj : ∀ a, toUnit (Over.mk (spMap φ ≫ t)) ≫ o.eta a = j ≫ lvR a := fun a => by
    simp only [lvR, ← Category.assoc]; congr 1
  have hj' : ∀ a, toUnit (Over.mk (spMap φ' ≫ t)) ≫ o.eta a = j' ≫ lvR a := fun a => by
    simp only [lvR, ← Category.assoc]; congr 1
  let ρ : (Over.mk t ⟶ A) →* (Over.mk (spMap φ ≫ t) ⟶ A) :=
    { toFun := fun g => j ≫ g, map_one' := MonObj.comp_one _, map_mul' := fun g h => MonObj.comp_mul _ _ _ }
  let ρ' : (Over.mk t ⟶ A) →* (Over.mk (spMap φ' ≫ t) ⟶ A) :=
    { toFun := fun g => j' ≫ g, map_one' := MonObj.comp_one _, map_mul' := fun g h => MonObj.comp_mul _ _ _ }
  have hpull : ∀ {K : Type} [Field K] (ψ : R' →+* K) (n : ℕ) (g h : Over.mk t ⟶ A) (u : R'ˣ),
      Out.WeilIs A PP.L (n : ℤ) g h (unitOn u) →
      Out.WeilIs A PP.L (n : ℤ) ((Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) ≫ g)
        ((Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) ≫ h)
        (unitOn (Units.map ψ.toMonoidHom u)) := by
    intro K _ ψ n g h u H
    have H' := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds hA PP.isLB
      (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) H
    have e : Units.map (spMap ψ).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map ψ.toMonoidHom u) :=
      Units.ext (congrArg (fun q => q.hom (u : R')) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))).symm
    exact e ▸ H'
  have hetapow : ∀ a, o.eta a ^ N = 1 := by
    intro a
    have : ∀ m : ℕ, o.eta (m • a) = o.eta a ^ m := by
      intro m
      induction m with
      | zero =>
        have h0 := o.eta_add 0 0
        rw [add_zero] at h0
        rw [zero_smul, pow_zero]
        exact left_eq_mul.1 h0 |>.symm ▸ rfl
      | succ m ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]
    rw [← this]; exact o.eta_ker a
  have hpow : ∀ a, lvR a ^ N = 1 := fun a => by
    simp only [lvR]; rw [← MonObj.comp_pow, hetapow, MonObj.comp_one]
  have h1 : ∀ n, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k φ).1
  have h2 : ∀ n, 0 < n → n.Coprime p → ∀ x : Over.mk (spMap φ ≫ t) ⟶ A, x ^ n = 1 →
      ∃ g : Over.mk t ⟶ A, g ^ n = 1 ∧ ρ g = x :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k φ).2
  have h3 : ∀ n, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 → ρ' g = ρ' h → g = h :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k' φ').1
  have h4 : ∀ n, 0 < n → n.Coprime p → ∀ x : Over.mk (spMap φ' ≫ t) ⟶ A, x ^ n = 1 →
      ∃ g : Over.mk t ⟶ A, g ^ n = 1 ∧ ρ' g = x :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k' φ').2
  have h5 := fun n (hn : 0 < n) (hnp : n.Coprime p) =>
    (GlobalTheory.rootsOfUnity_map_bijective_of_henselian R' k φ n hn (hRu n hn hnp))
  have h6 := fun n (hn : 0 < n) (hnp : n.Coprime p) =>
    (GlobalTheory.rootsOfUnity_map_bijective_of_henselian R' k' φ' n hn (hRu n hn hnp))
  have h7 : ∀ (c : D.O) (g h : Over.mk t ⟶ A), (g * h) ≫ o.act.act c = (g ≫ o.act.act c) * (h ≫ o.act.act c) := by
    intro c g h
    haveI := o.act.hom c
    exact MonObj.mul_comp _ _ _
  have h8 : ∀ c, (1 : Over.mk (spMap φ' ≫ t) ⟶ A) ≫ o.act.act c = 1 := by
    intro c
    haveI := o.act.hom c
    exact MonObj.one_comp _
  have h9 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 →
      ∃ u : R'ˣ, u ^ n = 1 ∧ Out.WeilIs A PP.L (n : ℤ) (ρ g) (ρ h) (unitOn (Units.map φ.toMonoidHom u)) ∧
        Out.WeilIs A PP.L (n : ℤ) (ρ' g) (ρ' h) (unitOn (Units.map φ'.toMonoidHom u)) := by
    intro n hn hnp g h hg hh
    obtain ⟨u, hu, H⟩ := GlobalTheory.WeilRootLocal.exists_weilIs_root_local S A hA PP cub R' t n g h hg hh
    exact ⟨u, hu, hpull φ n g h u H, hpull φ' n g h u H⟩
  have h10 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ (x y : Over.mk (spMap φ ≫ t) ⟶ A) (c c' : kˣ),
      Out.WeilIs A PP.L (n : ℤ) x y (unitOn c) → Out.WeilIs A PP.L (n : ℤ) x y (unitOn c') → c = c' :=
    fun n _ _ x y c c' h h' => GlobalTheory.weilIs_unique_fieldPoint S A PP.L PP.isLB k (spMap φ ≫ t) n x y c c' h h'
  obtain ⟨I', hI'⟩ := GlobalTheory.UPel.HT.TateTransportO.transport_alg D (R := R') (k := k) (k' := k')
    (QR := Over.mk t ⟶ A) (Q := Over.mk (spMap φ ≫ t) ⟶ A) (Q' := Over.mk (spMap φ' ≫ t) ⟶ A)
    (fun a b => mul_comm a b) (fun c g => g ≫ o.act.act c) (fun c g => g ≫ o.act.act c)
    (fun c g => g ≫ o.act.act c)
    (fun n g g' c => Out.WeilIs A PP.L n g g' (unitOn c)) (fun n g g' c => Out.WeilIs A PP.L n g g' (unitOn c))
    ρ ρ' (Units.map φ.toMonoidHom) (Units.map φ'.toMonoidHom)
    h1 h2 h3 h4 (fun n hn hnp => (h5 n hn hnp).1) (fun n hn hnp => (h5 n hn hnp).2)
    (fun n hn hnp => (h6 n hn hnp).1)
    h7 (fun c g => (Category.assoc j g (o.act.act c)).symm) (fun c g => (Category.assoc j' g (o.act.act c)).symm)
    h8 h9 h10 I
  exact ⟨I', fun a => (hj' a).trans (hI' N hN hNp a (lvR a) (hpow a) ((hj a).symm.trans (hI a)))⟩

theorem geomAt_iff_of_specializes {b : Base D R} {N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {s : S ⟶ Sp R}
    (o : PreEta b N s) {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    (x : Sp k ⟶ S) (x' : Sp k' ⟶ S) (u : Sp k) (u' : Sp k') (h : x'.base u' ⤳ x.base u) :
    o.GeomAt k x ↔ o.GeomAt k' x' := by
  obtain ⟨R', _, _, _, r, i, i', rfl, rfl⟩ := GlobalTheory.geomPoints_factor_henselian_of_specializes x x' u u' h
  exact ⟨geomAt_transport hN hNp o R' r i i', geomAt_transport hN hNp o R' r i' i⟩

end GlobalTheory.UPel.HT.LevelClopen

namespace GlobalTheory.UPel.HT

open LevelClopen

theorem PreEta.exists_clopen_geomAt : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R)
    (o : PreEta b N s), ∃ U : S.Opens, IsClosed (U : Set S) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S), (Set.range x.base ⊆ (U : Set S) ↔ o.GeomAt k x) := by
  intro p _ D R _ b N hN3 hNp S _ s o
  have hN : 0 < N := by omega
  let U : Set S := {z | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ S),
    z ∈ Set.range x.base ∧ o.GeomAt k x}
  have hclo : IsClopen U := by
    refine GlobalTheory.SpecGenClopen.isClopen_of_specializes_iff S U fun z w hzw => ?_
    constructor
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := GlobalTheory.FinEt.exists_algClosed_point S w
      obtain ⟨u', hu'⟩ : w ∈ Set.range x'.base := by rw [show Set.range x'.base = {w} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩,
        (geomAt_iff_of_specializes hN hNp o x' x u' u ?_).2 hG⟩
      rw [hu, hu']
      exact hzw
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := GlobalTheory.FinEt.exists_algClosed_point S z
      obtain ⟨u', hu'⟩ : z ∈ Set.range x'.base := by rw [show Set.range x'.base = {z} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩,
        (geomAt_iff_of_specializes hN hNp o x x' u u' ?_).1 hG⟩
      rw [hu, hu']
      exact hzw
  refine ⟨⟨U, hclo.isOpen⟩, hclo.isClosed, fun k _ _ x => ⟨fun hx => ?_,
    fun hG z hz => ⟨k, inferInstance, inferInstance, x, hz, hG⟩⟩⟩
  let pt : Sp k := (⊥ : PrimeSpectrum k)
  obtain ⟨k', _, _, x', ⟨u', hu'⟩, hG'⟩ := hx ⟨pt, rfl⟩
  exact (geomAt_iff_of_specializes hN hNp o x x' pt u' (hu' ▸ specializes_rfl)).2 hG'

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermSystemHeightFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}} {N : ℕ}
  {s : S ⟶ Sp R}

theorem act_zero_eq_one_wvs (o : Obj b N s) : o.act.act 0 = 1 := by
  have h := o.act.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

def ptModuleWvs (o : Obj b N s) (T : Over S) : Module (𝓞 D.F) (Additive (T ⟶ o.A)) where
  smul a g := Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
  one_smul g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 1)) = g
    rw [map_one, o.act.one, Category.comp_id]; rfl
  mul_smul a c g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a * c))) =
      Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
    rw [map_mul, o.act.mul, Category.assoc]
  smul_zero a := by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    show Additive.ofMul ((1 : T ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) = Additive.ofMul 1
    rw [one_comp]
  smul_add a g h := by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    show Additive.ofMul ((g.toMul * h.toMul) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) =
      Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) * (h.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)))
    rw [mul_comp]
  add_smul a c g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a + c))) =
      Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) * (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)))
    rw [map_add, o.act.add, comp_mul]
  zero_smul g := by
    show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 0)) = Additive.ofMul 1
    rw [map_zero, act_zero_eq_one_wvs, comp_one]

attribute [local instance] ptModuleWvs

theorem smul_toMul_wvs (o : Obj b N s) (T : Over S) (a : 𝓞 D.F) (g : Additive (T ⟶ o.A)) :
    (a • g).toMul = g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) := rfl

def kerWSubWvs (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) [IsMonHom ψ]
    (hl : ∀ a : 𝓞 D.F, o.act.act (algebraMap (𝓞 D.F) D.O a) ≫ ψ = ψ ≫ o'.act.act (algebraMap (𝓞 D.F) D.O a))
    (w : Ideal (𝓞 D.F)) (T : Over S) : Submodule (𝓞 D.F) (Additive (T ⟶ o.A)) where
  carrier := {g | g.toMul ≫ ψ = 1 ∧ KilledBy o w g.toMul}
  zero_mem' := by
    refine ⟨one_comp ψ, fun a _ => ?_⟩
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    exact one_comp _
  add_mem' {g h} hg hh := by
    refine ⟨?_, fun a ha => ?_⟩
    · show (g.toMul * h.toMul) ≫ ψ = 1
      rw [mul_comp, hg.1, hh.1, _root_.mul_one]
    · haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
      show (g.toMul * h.toMul) ≫ _ = 1
      rw [mul_comp, hg.2 a ha, hh.2 a ha, _root_.mul_one]
  smul_mem' c g hg := by
    refine ⟨?_, fun a ha => ?_⟩
    · show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ ψ = 1
      haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O c)
      rw [Category.assoc, hl, ← Category.assoc, hg.1, one_comp]
    · show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
      rw [Category.assoc, ← o.act.mul, ← map_mul, mul_comm, map_mul, o.act.mul, ← Category.assoc, hg.2 a ha,
        one_comp]

theorem card_kerW_eq_pow : ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {S : Scheme.{0}} {N : ℕ} {s : S ⟶ Sp R} (o o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsMonHom ψ →
    (∀ a : 𝓞 D.F, o.act.act (algebraMap (𝓞 D.F) D.O a) ≫ ψ = ψ ≫ o'.act.act (algebraMap (𝓞 D.F) D.O a)) →
    ∀ (w : Ideal (𝓞 D.F)), w.IsMaximal → ∀ {k : Type} [Field k] (y : Sp k ⟶ S),
    Finite {g : Over.mk y ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} →
    ∃ j' : ℕ, Nat.card {g : Over.mk y ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ j' := by
  intro p _ D R _ b S N s o o' ψ hψ hl w hw k _ y hfin
  haveI := hψ
  let K := kerWSubWvs o o' ψ hl w (Over.mk y)
  let e : K ≃ {g : Over.mk y ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} :=
    { toFun := fun x => ⟨x.1.toMul, x.2⟩
      invFun := fun g => ⟨Additive.ofMul g.1, g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Finite K := Finite.of_equiv _ e.symm
  have htor : Module.IsTorsionBySet (𝓞 D.F) K (w : Set (𝓞 D.F)) := by
    intro x a
    apply Subtype.ext
    show Additive.ofMul (x.1.toMul ≫ o.act.act (algebraMap _ _ a.1)) = Additive.ofMul 1
    rw [x.2.2 a.1 a.2]
  letI := Ideal.Quotient.field w
  letI : Module (𝓞 D.F ⧸ w) K := htor.module
  have hne : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hw (NumberField.RingOfIntegers.not_isField D.F)
  haveI : Finite (𝓞 D.F ⧸ w) := Ideal.finiteQuotientOfFreeOfNeBot w hne
  letI := Fintype.ofFinite (𝓞 D.F ⧸ w)
  letI := Fintype.ofFinite K
  refine ⟨Module.finrank (𝓞 D.F ⧸ w) K, ?_⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := 𝓞 D.F ⧸ w),
    Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsAreConstantAbelianSchemeNoetheria
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

open Opposite TopologicalSpace

theorem const_of_isAbelianScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → Const A.hom := by
  intro R _ _ A _ hA
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  haveI : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth A.hom
  have hbij := ((GlobalTheory.ProperFunctions.functions_of_isProper).2.2 R A.left A.hom).1
  intro g hg
  have hc : ∀ (U V : A.left.affineOpens) (h : V.1 ≤ U.1),
      A.left.presheaf.map (homOfLE h).op (g (op U)) = g (op V) := by
    intro U V h
    have e := congrFun (congrFun (congrFun hg (op U)) (op V)) (homOfLE h).op
    exact (sub_eq_zero.1 e).symm
  obtain ⟨t, ht, -⟩ := A.left.sheaf.existsUnique_gluing' (fun U : A.left.affineOpens ↦ U.1) ⊤
    (fun _ ↦ homOfLE le_top) (iSup_affineOpens_eq_top A.left).ge (fun U ↦ g (op U)) (by
      intro U V
      refine A.left.sheaf.eq_of_locally_eq' (fun W : {W : A.left.affineOpens // W.1 ≤ U.1 ⊓ V.1} ↦ W.1.1)
        (U.1 ⊓ V.1) (fun W ↦ homOfLE W.2) ?_ _ _ fun W ↦ ?_
      · intro x hx
        obtain ⟨W, hW, hxW, hWUV⟩ := Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens hx
        exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWUV⟩, hxW⟩
      · dsimp only
        have e : ∀ {a b c : Opens A.left} (f : b ⟶ a) (f' : c ⟶ b) (x : Γ(A.left, a)),
            A.left.presheaf.map f'.op (A.left.presheaf.map f.op x) = A.left.presheaf.map (f' ≫ f).op x := by
          intros; simp
        refine (e _ _ _).trans ((hc U W.1 (W.2.trans inf_le_left)).trans
          ((hc V W.1 (W.2.trans inf_le_right)).symm.trans (e _ _ _).symm)))
  obtain ⟨r, hr⟩ := hbij.2 t
  refine ⟨r, fun U ↦ ?_⟩
  rw [← ht U.unop, ← hr]
  rfl

end GlobalTheory.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedBundleSpecialFibreGeneratorStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_bundle_special_fibre_generator : ∀ (F : Type) [Field F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), (∀ x y : X, ∃ u, RatioProp h x y u) → ∃ t : ((glueLB h).pull (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.reducedSpecialι s)).Gen, t.IsGen := by
  first | exact @GlobalTheory.UnitGlue.glueLB_reducedSpecial_gen | exact GlobalTheory.UnitGlue.glueLB_reducedSpecial_gen | (intros; apply GlobalTheory.UnitGlue.glueLB_reducedSpecial_gen <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedGeneratorIsGeneratorStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_generator_is_generator : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), (∀ x y : X, ∃ u, RatioProp h x y u) → (sigGen h s).IsGen := by
  first | exact @GlobalTheory.UnitGlue.sigGen_isGen_of_ratio | exact GlobalTheory.UnitGlue.sigGen_isGen_of_ratio | (intros; apply GlobalTheory.UnitGlue.sigGen_isGen_of_ratio <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedLineBundleInvertibleStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_line_bundle_invertible : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), IsIntegral X → (Xw : Set X).Nonempty → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (∀ x y : X, ∃ u, RatioProp h x y u) → (glueLB h).IsLB := by
  first | exact @GlobalTheory.UnitGlue.glueLB_isLB | exact GlobalTheory.UnitGlue.glueLB_isLB | (intros; apply GlobalTheory.UnitGlue.glueLB_isLB <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramBoundStatement
section
noncomputable section

open GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovTop

theorem gram_of_hypotheses (_h : Hypotheses2) : Gram :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, le_rfl, 0, fun _ _ _ _ p hp i =>
      ⟨GlobalTheory.T.row_norm_has_gram p hp.1 hp.2 i, GlobalTheory.T.row_lattice_finitely_generated p hp.1 hp.2 i, GlobalTheory.T.row_good_lattice_ne_bot p hp.1 hp.2 i, GlobalTheory.T.row_good_weight_dictionary p hp.1 hp.2 i⟩⟩⟩⟩

end GlobalTheory.CovTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftAbelianSchemeOfSquareZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem liftObj_sq : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftObj (divided₂ hI) π := by
  intro P R R₀ _ _ I hI π hπ hk H g A₀ _ A' _ i' h' hA' hg' F hF
  have hn : IsNilpotent (RingHom.ker π) := ⟨2, hk ▸ hI⟩
  obtain ⟨X, i, h, hX, hFil⟩ := H.exists_lift h' hA' hg' hF
  have hA₀ : IsAbelianScheme A₀ := PolPull.isAbelianScheme_of_isGrpPullback hA' h'
  have hg₀ : SmoothOfRelativeDimension g A₀.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h'.1 hg'
  obtain ⟨e, he, he₀⟩ := GlobalTheory.T.exists_section_lift_smooth_nilpotent_thickening R R₀ π hπ hn X A₀ i h hX (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left
    (Over.w (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀))
  have w : ((fst A₀ A₀).left ≫ i) ≫ X.hom = ((snd A₀ A₀).left ≫ i) ≫ X.hom := by
    rw [Category.assoc, Category.assoc, h.w, Over.w_assoc, Over.w_assoc]
  have hl₁ : (Limits.pullback.lift _ _ w : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left) ≫ (fst X X).left
      = (fst A₀ A₀).left ≫ i := Limits.pullback.lift_fst _ _ _
  have hl₂ : (Limits.pullback.lift _ _ w : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left) ≫ (snd X X).left
      = (snd A₀ A₀).left ≫ i := Limits.pullback.lift_snd _ _ _
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_lift_shearMap_squareZero_abelianSchemes R R₀ I hI π hπ hk H g g A₀ A₀ A' A' i' i' h' h' hA' hA' hg' hg' X X i i h h hX hX
    e e he he he₀ he₀ _ hl₁ hl₂ (𝟙 A₀) (fun d hd ↦ by rw [push_id]; exact hd)
  have hμ : (fst A₀ A₀ ≫ 𝟙 A₀) * snd A₀ A₀ = μ[A₀] := by
    rw [Category.comp_id, Hom.mul_def, lift_fst_snd, Category.id_comp]
  rw [hμ] at hm
  obtain ⟨_, hp, hab⟩ := GlobalTheory.T.exists_grpObj_isAbelianScheme_smoothLift_nilpotent R R₀ π hπ hn A₀ hA₀ X i h hX e he he₀ _ hl₁ hl₂ m hm
  have hg : SmoothOfRelativeDimension g X.hom := GlobalTheory.T.smoothOfRelativeDimension_of_nilpotent_reduction R R₀ π hπ hn g X A₀ i h hX hg₀
  exact ⟨X, _, i, hp, hab, hg, (schemeFil_eq_liftFil _ hp (P.1 R X g hab hg).1).symm.trans hFil⟩

end GlobalTheory.SqLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingPreservingTransportOfRankZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasMarkingPreservingTransport_of_rank_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (e : c.F →+* ℂ), D.p + D.q = 0 → HasTransport Xo c U e := by
  first | exact @GlobalTheory.DetLine.RankZero.hasTransport_of_rank_zero | exact GlobalTheory.DetLine.RankZero.hasTransport_of_rank_zero | (intros; apply GlobalTheory.DetLine.RankZero.hasTransport_of_rank_zero <;> assumption)
end

