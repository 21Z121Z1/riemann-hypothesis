import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3595
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankComponentWeightInvariance
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3593
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0698
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0716
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3594
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3552

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDividingLabelsIffClassZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep.IntLabel

section
variable {G X : Type} [AddCommGroup G] [AddCommGroup X] {N : ℕ} {Y : G → X → Prop}

theorem yy_zero (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ CongMod N mu' mu))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) : Y 0 0 := by
  obtain ⟨mu, hmu⟩ := h1 0
  have h2 := h4 0 0 mu mu hmu hmu
  rw [add_zero] at h2
  have hc := (h3 0 mu (mu + mu) hmu).1 h2
  refine (h3 0 mu 0 hmu).2 ?_
  obtain ⟨w, hw⟩ := hc
  have e : mu = N • w := add_left_cancel (a := mu) (by simpa using hw)
  exact ⟨-w, by simp [e]⟩

theorem yy_neg (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ CongMod N mu' mu))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) {a : G} {mu : X} (ha : Y a mu) :
    Y (-a) (-mu) := by
  obtain ⟨mu', h'⟩ := h1 (-a)
  have h0 := h4 a (-a) mu mu' ha h'
  rw [add_neg_cancel] at h0
  have hc := (h3 0 0 (mu + mu') (yy_zero h1 h3 h4)).1 h0
  refine (h3 (-a) mu' (-mu) h').2 ?_
  obtain ⟨w, hw⟩ := hc
  rw [zero_add] at hw
  refine ⟨-w, ?_⟩
  rw [smul_neg, ← hw]
  abel

theorem yy_sub (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ CongMod N mu' mu))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) {a b : G} {mu nu : X} (ha : Y a mu)
    (hb : Y b nu) : Y (a - b) (mu - nu) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h4 _ _ _ _ ha (yy_neg h1 h3 h4 hb)

theorem yy_nsmul (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ CongMod N mu' mu))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) (k : ℕ) {a : G} {mu : X} (ha : Y a mu) :
    Y (k • a) (k • mu) := by
  induction k with
  | zero => simpa using yy_zero h1 h3 h4
  | succ k ih => rw [succ_nsmul, succ_nsmul]; exact h4 _ _ _ _ ih ha

theorem mem_closure_iff (p J : ℕ) (hJ : 2 ≤ J) (hN : N = p ^ J) (hG : ∀ a : G, N • a = 0)
    (htor : ∀ b : G, p • b = 0 → ∃ c, b = p ^ (J - 1) • c) (htf : ∀ x : X, p ^ (J - 1) • x = 0 → x = 0)
    (h1 : ∀ a, ∃ mu, Y a mu) (h2 : ∀ mu, ∃ a, Y a mu)
    (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ CongMod N mu' mu))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) (S : Set G) (hS : ∀ a ∈ S, Y a 0)
    (hT : ∀ a, Y a 0 → ∃ b, p • b = 0 ∧ a + b ∈ S) (a : G) : a ∈ AddSubgroup.closure S ↔ Y a 0 := by
  constructor
  · intro ha
    induction ha using AddSubgroup.closure_induction with
    | mem x hx => exact hS x hx
    | zero => exact yy_zero h1 h3 h4
    | add x y _ _ hx hy => simpa using h4 x y 0 0 hx hy
    | neg x _ hx => simpa using yy_neg h1 h3 h4 hx
  · intro ha
    obtain ⟨b, hb, hab⟩ := hT a ha
    have hYb : Y b 0 := by simpa using yy_sub h1 h3 h4 (hS _ hab) ha
    obtain ⟨c, rfl⟩ := htor b hb
    obtain ⟨muc, hc⟩ := h1 c
    have hcong := (h3 _ _ _ (yy_nsmul h1 h3 h4 (p ^ (J - 1)) hc)).1 hYb
    have hw : ∃ w : X, muc = p • w := by
      obtain ⟨w, hw⟩ := hcong
      refine ⟨-w, ?_⟩
      have e : p ^ (J - 1) • (muc + p • w) = 0 := by
        rw [smul_add, smul_smul, ← pow_succ, Nat.sub_add_cancel (by omega), ← hN]
        exact hw.symm
      rw [smul_neg, eq_neg_iff_add_eq_zero]
      exact htf _ e
    obtain ⟨w, hmu⟩ := hw
    obtain ⟨c', hc'⟩ := h2 w
    have hk : Y (c - p • c') 0 := by
      have := yy_sub h1 h3 h4 hc (yy_nsmul h1 h3 h4 p hc')
      rwa [← hmu, sub_self] at this
    obtain ⟨bk, hbk, hkS⟩ := hT _ hk
    have hbk0 : p ^ (J - 1) • bk = 0 := by
      obtain ⟨e, he⟩ : ∃ e, J - 1 = e + 1 := ⟨J - 2, by omega⟩
      rw [he, pow_succ, mul_smul, hbk, smul_zero]
    have key : p ^ (J - 1) • c = p ^ (J - 1) • ((c - p • c') + bk) := by
      rw [smul_add, hbk0, add_zero, smul_sub, smul_smul, ← pow_succ, Nat.sub_add_cancel (by omega), ← hN, hG, sub_zero]
    have hbcl : p ^ (J - 1) • c ∈ AddSubgroup.closure S := by
      rw [key]; exact nsmul_mem (AddSubgroup.subset_closure hkS) _
    have e : a = (a + p ^ (J - 1) • c) - p ^ (J - 1) • c := by abel
    rw [e]
    exact sub_mem (AddSubgroup.subset_closure hab) hbcl

theorem zmod_tors {p J M : ℕ} (hp : 0 < p) (hJ : 1 ≤ J) (hM : M = p ^ J) (x : ZMod M) (hx : p • x = 0) :
    ∃ y : ZMod M, x = p ^ (J - 1) • y := by
  subst hM
  haveI : NeZero (p ^ J) := ⟨pow_ne_zero _ hp.ne'⟩
  have h1 : p ^ J ∣ p * x.val := by
    rw [← CharP.cast_eq_zero_iff (ZMod (p ^ J)) (p ^ J)]
    push_cast
    rw [ZMod.natCast_zmod_val]
    rwa [nsmul_eq_mul] at hx
  have h2 : p ^ (J - 1) ∣ x.val := by
    have e : p ^ J = p * p ^ (J - 1) := by rw [← pow_succ']; congr 1; omega
    have h1' : p * p ^ (J - 1) ∣ p * x.val := by rw [← e]; exact h1
    exact Nat.dvd_of_mul_dvd_mul_left hp h1'
  obtain ⟨q, hq⟩ := h2
  refine ⟨(q : ZMod (p ^ J)), ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [hq, nsmul_eq_mul]
  push_cast
  ring

end
end GlobalTheory.GSep.IntLabel

namespace GlobalTheory.GSep

open GlobalTheory.GSep.IntLabel in

theorem mem_HH_iff_yy_zero : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ ↔ 𝔪.YY a 0 := by
  intro I X₁ z₁ act x₀ hx₀ V _ _ _ ev X _ t δ 𝔪 a
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V ev X t δ 𝔪
  obtain ⟨j, hj, hr⟩ := X₁.ρ.r_eq
  have hp : 0 < X₁.ρ.n := X₁.ρ.n_prime.pos
  have hk := X₁.ρ.two_le
  have hN : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j + X₁.ρ.k * 2) := by rw [hr, X₁.ρ.N_eq, pow_add, pow_mul]
  have hJ : 2 ≤ j + X₁.ρ.k * 2 := by omega
  have hG : ∀ b : X₁.S.Gam, (X₁.S.r * X₁.S.N) • b = 0 := fun b => by
    funext v
    simp [nsmul_eq_mul]
  have htor : ∀ b : X₁.S.Gam, X₁.ρ.n • b = 0 → ∃ c : X₁.S.Gam, b = X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • c := by
    intro b hb
    have hv : ∀ v, ∃ y : ZMod (X₁.S.r * X₁.S.N), b v = X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • y := fun v =>
      zmod_tors hp (by omega) hN (b v) (by simpa using congrFun hb v)
    choose c hc using hv
    exact ⟨c, funext fun v => by simpa using hc v⟩
  have htf : ∀ x : X, X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • x = 0 → x = 0 := by
    intro x hx
    have hq : X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) ≠ 0 := pow_ne_zero _ hp.ne'
    have he : ((X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) : ℕ) : ℤ) • 𝔪.e₈ x = 0 := by
      rw [natCast_zsmul, ← map_nsmul, hx, map_zero]
    have h0 : 𝔪.e₈ x = 0 := (smul_eq_zero.1 he).resolve_left (by exact_mod_cast hq)
    exact 𝔪.e₈.injective (h0.trans (map_zero _).symm)
  rw [ThetaSys.HH]
  exact mem_closure_iff (X₁.ρ.n) (j + X₁.ρ.k * 2) hJ hN hG htor htf h1 h2 h3 h4 _
    (fun b hb => GlobalTheory.T.thetaMember_dividing_label_class_zero I X₁ z₁ act V ev X t δ 𝔪 b hb)
    (fun b hb => GlobalTheory.T.exists_torsionTranslate_of_classZero_dividing I X₁ z₁ act V ev X t δ 𝔪 x₀ hx₀ b hb) a

end GlobalTheory.GSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOverAntitoneComb
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtNef

open ReciprocityTheory.ChartRestriction.G GlobalTheory.CechPic in

theorem nefOver_iff_of_isometric {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {L L' : HermLB p}
    (h : L.Isometric L') (l : ℕ) : NefOver L l ↔ NefOver L' l := by
  obtain ⟨w, hw, -⟩ := h
  have e : cls L.B L.isLB = cls L'.B L'.isLB := (cls_eq_iff _ _).2 ⟨w, hw⟩
  have key : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)],
      topSelfIntersection κ (L.B.pull i) 1 = topSelfIntersection κ (L'.B.pull i) 1 := fun Z i κ _ _ =>
    interNum_congr_cls κ _ (fun _ => LB.isLB_pull L.isLB i) (fun _ => LB.isLB_pull L'.isLB i) fun _ => by
      rw [cls_pull L.isLB, cls_pull L'.isLB, e]
  constructor <;> intro H Z i _ _ κ _ _ _ _ hd
  · rw [← key]; exact H Z i κ hd
  · rw [key]; exact H Z i κ hd

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem map_genericPoint {V' V : Cover Y} (g : V'.G ⟶ V.G) (h : g ≫ V.π = V'.π) :
    g (genericPoint V'.G) = genericPoint V.G := by
  have key (W : Cover Y) : W.π (genericPoint W.G) = genericPoint Y.X := by
    have := (genericPoint_spec W.G).image W.π.continuous
    rw [Set.image_univ, W.π.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  obtain ⟨U, hU, e⟩ := isDiscrete_iff_forall_exists_isOpen.mp (V.π.isDiscrete_preimage_singleton (genericPoint Y.X))
    (g (genericPoint V'.G)) (by rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, h, key]; rfl)
  have h₁ : g (genericPoint V'.G) ∈ U := (e.ge rfl).1
  exact (e.le ⟨(genericPoint_specializes _).mem_open hU h₁, key V⟩).symm

theorem surjective_of_lies {V' V : Cover Y} (π : V'.X ⟶ V.X) (hπ : π ≫ V.p = V'.p) (h : Lies V' V π) :
    Function.Surjective π := by
  obtain ⟨g, h₁, h₂⟩ := h
  have hη := (GlobalTheory.CoverDeg.map_genericPoint_and_deg F Y V V' π hπ g h₁.symm h₂ (map_genericPoint g h₂)).1
  have : IsProper V.p := (isProper_and_exists_isAmpleLB_of_isProjOver V.ar.isProjOver).1
  have : IsProper V'.p := (isProper_and_exists_isAmpleLB_of_isProjOver V'.ar.isProjOver).1
  have : IsProper (π ≫ V.p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π V.p
  have hc : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
  have hm : genericPoint V.X ∈ Set.range π := ⟨_, hη⟩
  have : closure {genericPoint V.X} ⊆ Set.range π := hc.closure_subset_iff.2 (Set.singleton_subset_iff.2 hm)
  rw [(genericPoint_spec V.X).def] at this
  exact fun z => this (Set.mem_univ z)

end GlobalTheory.HtNef

open GlobalTheory.HtNef in

theorem GlobalTheory.HtNef.nefOver_comb_root : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (V : Cover (O.var c)) (L : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (L x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) → ∀ n : D.what₂.Tau → Fin O.N → ℤ, (∀ τ, Antitone (n τ)) → ∀ l ∈ Q, l.Prime → NefOver (ArInt.comb L fun x => -n x.1 x.2) l := by
  intro hP hH D O hC hf A T H h c Q V L hL n hn l hlQ hl
  obtain ⟨V₀, M, hM, hMn⟩ := GlobalTheory.T.combined_metrized_bundle_nef_antitone hP hH D O hC hf A T H h c Q l hlQ hl
  obtain ⟨V', π, π₀, hπ, hπ₀, l₁, l₀⟩ := GlobalTheory.T.common_refinement_covers _ _ V V₀
  have hs := surjective_of_lies π hπ l₁
  obtain ⟨g₁, e₁, f₁⟩ := l₁
  obtain ⟨g₀, e₀, f₀⟩ := l₀
  have hL' x := GlobalTheory.T.norms_pullback_along_cover _ _ V V' π hπ g₁ e₁.symm f₁ (map_genericPoint g₁ f₁) (L x) _ _ _ (hL x)
  have hM' x := GlobalTheory.T.norms_pullback_along_cover _ _ V₀ V' π₀ hπ₀ g₀ e₀.symm f₀ (map_genericPoint g₀ f₀) (M x) _ _ _ (hM x)
  have iso x := GlobalTheory.T.isometric_of_same_norms _ _ V' _ _ _ _ _ (hL' x) (hM' x)
  have n₀ : NefOver ((ArInt.comb M fun x => -n x.1 x.2).pull π₀ hπ₀) l :=
    GlobalTheory.T.nef_hermitian_bundle_pullback _ _ _ _ _ V₀.ar.isProjOver V'.ar.isProjOver π₀ hπ₀ _ l hl (hMn n hn)
  have i₁ := (isometric_comb_pull M (fun x => -n x.1 x.2) π₀ hπ₀).symm
  have i₂ := (isometric_comb_congr iso (fun x => -n x.1 x.2)).symm
  have i₃ := isometric_comb_pull L (fun x => -n x.1 x.2) π hπ
  have n₁ := (nefOver_iff_of_isometric (i₁.trans (i₂.trans i₃)) l).1 n₀
  exact GlobalTheory.T.nef_of_surjective_pullback_nef _ _ _ _ _ V.ar.isProjOver V'.ar.isProjOver π hπ hs _ l hl n₁

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QkPointGaloisFixedUpToEquivDividedDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qkPoint_galois_fixed_up_to_equiv_divided_data : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p p' : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M'), QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv P.D.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  first | exact @GlobalTheory.DivGalFix.qkExt_equiv_of_divFrom | exact GlobalTheory.DivGalFix.qkExt_equiv_of_divFrom | (intros; apply GlobalTheory.DivGalFix.qkExt_equiv_of_divFrom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankComponentWeightInvarianceStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_component_weight_invariance : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u la : AllWt.Weight (T.Q.Dw j)) (n a : ℕ), GapGe (((CompHt.dimFlag (T.Q.Dw j) + 3) * ((CompHt.dimFlag (T.Q.Dw j) + 1).choose 2 + 4 * ((T.Q.Dw j).p + (T.Q.Dw j).q) + CompHt.dimFlag (T.Q.Dw j) + 3) : ℕ) : ℤ) u → (∀ τ, Antitone (la τ)) → (∀ τ, Antitone ((n : ℤ) • u τ - la τ)) → (n : ℝ) * CompHt.topDeg Y.U Z u < (a + 1) * Y.dg u Z → Y.rkC la Z ≤ ((a + CompHt.dimFlag (T.Q.Dw j)).choose (CompHt.dimFlag (T.Q.Dw j)) : ℕ) * Y.dg u Z := by
  first | exact @GlobalTheory.JetRank.rkC_le | exact GlobalTheory.JetRank.rkC_le | (intros; apply GlobalTheory.JetRank.rkC_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfMumfordBundleIsoUniversal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

namespace GlobalTheory.MumAmple

theorem relAmple_of_lam_iso_univ : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (R' : Type) [CommRing R'] [IsNoetherianRing R'] (T : Sp R' ⟶ F.X) (B : Over (Sp R')) [GrpObj B] [IsCommMonObj B] (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A T β → IsSquare β β₂ → ∀ L : LB B.left, L.IsLB → LBIso (abelian₂ B L) (F.univ.P.pull β₂) → RelAmple B L := by
  intro o _ ζ g n F R' _ _ T B _ _ β β₂ hpb hsq L hL hiso
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback F.univ.ab hpb
  have := hB.proper
  have := hB.smooth
  refine ProperFinite.relAmple_of_geometricFibres B hL fun K _ _ y => ?_
  have hk := isGrpPullback_pullback B y
  have hkU := hk.comp hpb
  obtain ⟨⟨c, hc⟩, hprin⟩ := GlobalTheory.siegPre_pullback g n o ζ F.X (Sp K) F.s ((y ≫ T) ≫ F.s) (y ≫ T) F.univ rfl
  have hcp := hprin c hc F.princ
  obtain ⟨φc, φc₂, hcpb, hcsq, hcP, -⟩ := hc
  obtain ⟨L₀, h₀, hlam₀, ha₀⟩ := PolBundleLoc.exists_ample_root c.A c.ab c.isLB c.rig₁ c.rig₂ c.symm hcp.1
  have hk₀ := KTrivOfLam.kTriv_of_lam_iso _ c.A c.ab c.P c.isLB hcp.2 L₀ h₀ hlam₀
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hcpb hkU
  haveI := he
  let ψ : c.A.left ⟶ B.left := e.hom.left ≫ pullback.fst B.hom y
  have hψ : IsGrpPullback c.A B y ψ := by
    have := (isGrpPullback_of_iso e).comp hk
    rwa [Category.id_comp] at this
  obtain ⟨ψ₂, sψ⟩ := SiegPull.exists_isSquare hψ.1.w
  have hN : (L.pull ψ).IsLB := pull_isLB hL ψ
  have hlamN : LBIso (abelian₂ c.A (L.pull ψ)) ((abelian₂ B L).pull ψ₂) :=
    SiegPull.lbIso_lam_pull hψ ((CechPic.cls_eq_iff hN hN).1 rfl) sψ
  have hsq' : IsSquare (ψ ≫ β) (ψ₂ ≫ β₂) := SiegPull.isSquare_comp sψ hsq
  have hφ : ψ ≫ β = φc := by simpa [ψ, Category.assoc] using heφ
  have e₂ : ψ₂ ≫ β₂ = φc₂ := SiegPull.isSquare_unique hsq' hcsq hφ
  have hpullP : LBIso ((abelian₂ B L).pull ψ₂) (F.univ.P.pull (ψ₂ ≫ β₂)) := SiegPull.lbIso_pull_comp hiso ψ₂
  rw [e₂] at hpullP
  have iLN : (abelian₂ c.A (L.pull ψ)).IsLB := LB.isLB_linComb hN _ _
  have iL0 : (abelian₂ c.A L₀).IsLB := LB.isLB_linComb h₀ _ _
  have iLB : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hlam : CechPic.lam (CechPic.cls (L.pull ψ) hN) (fst c.A c.A) (snd c.A c.A) =
      CechPic.lam (CechPic.cls L₀ h₀) (fst c.A c.A) (snd c.A c.A) :=
    (CechPic.cls_cube_two hN _ _ iLN).symm.trans
      (((CechPic.cls_eq_iff iLN (pull_isLB iLB _)).2 hlamN).trans
        (((CechPic.cls_eq_iff (pull_isLB iLB _) (pull_isLB F.univ.isLB _)).2 hpullP).trans
          (((CechPic.cls_eq_iff c.isLB (pull_isLB F.univ.isLB _)).2 hcP).symm.trans
            (((CechPic.cls_eq_iff iL0 c.isLB).2 hlam₀).symm.trans (CechPic.cls_cube_two h₀ _ _ iL0)))))
  obtain ⟨hampN, -⟩ := AmpleKerFibre.relAmple_kTriv_of_lam_eq K c.A c.ab L₀ h₀ ha₀ hk₀ (L.pull ψ) hN hlam
  have : IsProper c.A.hom := c.ab.proper
  have hAN := (relAmple_iff_isAmpleLB_of_isAffine c.A hN).1 hampN
  haveI : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have h1 := hAN.pull_of_isAffineHom e.inv.left
  have h2 : LBIso ((L.pull ψ).pull e.inv.left) (L.pull (pullback.fst B.hom y)) := by
    have h3 := SiegPull.lbIso_pull_comp ((CechPic.cls_eq_iff hN hN).1 rfl) e.inv.left
    have ee : e.inv.left ≫ ψ = pullback.fst B.hom y := by
      simp only [ψ]
      rw [← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
    rwa [ee] at h3
  exact (isAmpleLB_congr (pull_isLB hN _) (pull_isLB hL _) h2).1 h1

end GlobalTheory.MumAmple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallModMaximalOfFrobeniusImageSmall
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecond

theorem small_second : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j)) l))) → ∀ j, ¬IsUnit (F.θ (b j)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hμ' hc k e he hA U hU b hW j
  have hC : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  obtain ⟨Θ, hΘ⟩ := frame_fraction_map p F.B O F.Q F.θ F.frame C hC
  have hcμ : (fun i => map F.θ (μ' i)) = c.μ := funext hc
  have hconst : ∀ i, constantCoeff (μ' i) = 0 := hμ'.const

  have hQL : ∀ i, QL c.μ ⊤ (map Θ (e i)) := fun i => hcμ ▸ ql_map hΘ μ' hconst (he.1 i)
  have hlog : ∀ i, cob1 (up C c.μ) (map Θ (e (Sum.inl i))) = 0 := fun i =>
    hcμ ▸ formalGroupLawCoboundaryOne_map_eq_zero hΘ μ' hconst (hA i).1
  obtain ⟨lb, hlb⟩ := GlobalTheory.T.quasiLogarithm_secondBlock_tangent_basis_dual_lie p C v O hv ε hε F G d c μ' hμ' hc k e he hA Θ hΘ

  have hT := GlobalTheory.T.frobenius_linearCombination_zero_left_ainfFrame p O ε F d k e U (fun i => (hU i).1) b
  have hC1 := GlobalTheory.T.coboundary_frobenius_commute_mod_p_quasiLog p O ε F d μ' hμ' (Fin d ⊕ Fin k) e he.1 (Sum.elim (fun _ => 0) b)
  obtain ⟨F₁, t, hF₁, hlin, hpβ, hα⟩ := GlobalTheory.T.frobenius_congruence_combination_over_integers p C v O hv ε F d c.μ μ' hμ' hc k e he.1 _ b hW hT hC1
  have ht := GlobalTheory.T.not_isUnit_coeff_of_coboundary_small' p C v O hv d c.μ c.isLaw t hlin hα
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integral_coboundaryOne_congr_frobenius p C v O hv d c.μ c.isLaw (map F.θ F₁) t ht
    (fun β => by rw [coeff_map]; exact hpβ β)
  have key : cob1 (up C c.μ) (comb (Sum.elim 0 fun j => F.θ (b j)) fun i => map Θ (e i)) =
      map (algebraMap O C) (map F.θ F₁) := by
    have h1 : (Sum.elim 0 fun j => F.θ (b j) : Fin d ⊕ Fin k → O) =
        fun i => F.θ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) i) := by
      funext i; rcases i with i | i <;> simp
    rw [h1, ← map_comb hΘ, ← hcμ, ← map_formalGroupLawCoboundaryOne_square hΘ μ' hconst, ← hF₁]
    ext α; simp [coeff_map, hΘ]
  refine GlobalTheory.T.tangent_coords_nonunit_alt p C v O hv G d c C hC k (fun i => map Θ (e i)) lb hQL hlb hlog
    (fun j => F.θ (b j)) u (fun α => ⟨_, hu α, ?_⟩) j
  rw [key, ← map_sub, coeff_map, map_sub]

end GlobalTheory.SmallSecond
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourierClassSumsDeeperFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem classSums_deeper : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 8 → Φ.X y) → Q → PadicAlgCl p) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (X₁.M.Z.presheaf.stalk z₁) B) (_ : Module.Finite (X₁.M.Z.presheaf.stalk z₁) B) (_ : Finite (B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B)) (𝔷 : Ideal B), Function.Injective (algebraMap (X₁.M.Z.presheaf.stalk z₁) B) ∧ (∀ b : B, (∀ σ : B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B, σ b = b) → b ∈ Set.range (algebraMap (X₁.M.Z.presheaf.stalk z₁) B)) ∧ 𝔷.IsMaximal ∧ k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod ℤ N (k y)) ∧ Φ.IsTerms W t ∧ Φ.ClassSums (X₁.S.r * X₁.S.N) N y₀ k t B 𝔷 := by
  intro g n F W Z i X₁ p _ z₁ Φ hΦ y₀ N₀
  obtain ⟨N, hN₀, hdvd, Ω₂, _, _, _, _, hcore⟩ := GlobalTheory.T.thetaFourier_classSums_mem_integralClosure_galois g n F W Z i X₁ p z₁ Φ hΦ y₀ N₀
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  obtain ⟨hdom, hfr, hic, hno⟩ := GlobalTheory.T.thetaSetup_stalk_noetherian_normal_fractionRing g n F W Z i X₁ z₁
  obtain ⟨hfin, hfinA, hinj, hfix⟩ := GlobalTheory.T.integralClosure_galois_finite_autGroup_invariants (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ Ω₂
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra
  obtain ⟨𝔷, hmax⟩ := Ideal.exists_maximal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)
  have hext := fun y => GlobalTheory.T.extend_integral_padic_evaluation_galois p (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) 𝔷 hinj hfix hmax (Φ.ev y) (Φ.ev_le y) (Φ.ev_lt y)
  choose ev' h1 h2 h3 using hext
  obtain ⟨k, Q, t, f, hk₀, hk, ht, hf, hcs, hgal⟩ := hcore 𝔷 hmax ev' h1 h2 h3
  refine ⟨N, hN₀, hdvd, k, Q, t, (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), inferInstance, inferInstance, inferInstance, hfin, hfinA, 𝔷, hinj, hfix, hmax, hk₀, hk, ht, ev', f, h1, h2, h3, hf, hcs, fun σ hσ => ?_⟩
  obtain ⟨γ, hdet, hN₁, hσf⟩ := hgal σ hσ
  refine ⟨γ, fun c x => ⟨0, ?_⟩, hdet, hN₁, hσf⟩
  have hm : (Φ.mod y₀) = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
  rw [smul_zero, add_zero]
  first
  | (rw [hm]; exact map_zsmul γ c x)
  | (simp only [hm]; exact map_zsmul γ c x)
  | exact map_smul γ c x

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermsCoefficientsUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_terms_coefficients_unique : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (b : X₁.S.Gam)
  (x x₂ : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (fr₂ : ∀ a, FrAt (x₂ a))
  (th th₂ : SecA 𝔪.A (FractionRing V) 1) (w₀ w₀₂ : W0 𝔪.U.toUnifPre) (s s₂ : Fam 𝔪.D.toPre (FractionRing V) 1)
  (g' g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
  (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
  (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
  𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g' o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g' w (x b) (fr b) →
  (∀ a, (x₂ a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
  (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
  (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀₂.IsGen →
  𝔪.U.ExpandsF (FractionRing V) 1 w₀₂ th₂ s₂ →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀₂ g₂ w₂ (x₂ b) (fr₂ b) →
  ∀ χ, coef s g' w χ = coef s₂ g₂ w₂ χ := by
  first | exact @GlobalTheory.GSep.TermsUniq.coef_eq | exact GlobalTheory.GSep.TermsUniq.coef_eq | (intros; apply GlobalTheory.GSep.TermsUniq.coef_eq <;> assumption)
end

