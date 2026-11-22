import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0113
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0114
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0115
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0116
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyTestModelToClosure

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.FullPoint

theorem hasGen_of_point {X Y : Scheme.{0}} {k : Type} [Field k] (p : Y ⟶ Sp k) {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {U : (Sp k).Opens} {s : Sp k} (hs : s ∈ U) {ψ : K → ((p ⁻¹ᵁ U).toScheme ⟶ X)}
    (hψ : ∀ i, ψ i = (p ⁻¹ᵁ U).ι ≫ φ i) (h : MulPull.HasGen L ψ ε) : MulPull.HasGen L φ ε := by
  obtain rfl : U = ⊤ := eq_top_iff.2 fun x _ => by
    rwa [Subsingleton.elim (α := PrimeSpectrum k) x s]
  have e : φ = fun i => Y.topIso.inv ≫ ψ i := funext fun i => by
    rw [hψ]
    exact ((Y.topIso.inv_hom_id_assoc _)).symm
  rw [e]
  exact MulPull.HasGen.pull h _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem lbIso_of_rosatiAdj {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    (hL : L.IsLB) {f g : A ⟶ A} (h : RosatiAdj A L f g) :
    LBIso (cubeLB A ![fst A A ≫ f, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ g] L) := by
  obtain ⟨U, hU, h⟩ := h (default : PrimeSpectrum k)
  have e := (PrimNorm.hasGen_iff hL _ _).1 (hasGen_of_point (A ⊗ A).hom hU (fun _ => rfl) h)
  refine (PrimNorm.lbIso_iff hL _ _ _ _).2 ((PrimNorm.prod_square_id _ _ (PrimNorm.cls L)).trans
    (Eq.trans ?_ (PrimNorm.prod_square_id _ _ (PrimNorm.cls L)).symm))
  rw [Fin.prod_univ_six] at e
  let m : ((A ⊗ A) ⟶ A) → PrimNorm.PullClass L (A ⊗ A).left := fun q => PrimNorm.cls L q.left
  have e' : m ((fst A A ≫ f) * snd A A) ^ (1 : ℤ) * m (fst A A ≫ f) ^ (-1 : ℤ) * m (snd A A) ^ (-1 : ℤ) *
      m (fst A A * (snd A A ≫ g)) ^ (-1 : ℤ) * m (fst A A) ^ (1 : ℤ) * m (snd A A ≫ g) ^ (1 : ℤ) = 1 := e
  show PrimNorm.diff₂ m _ _ = PrimNorm.diff₂ m _ _
  rw [← mul_inv_eq_one, ← e', PrimNorm.diff₂, PrimNorm.diff₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, zpow_neg, zpow_one]
  abel

theorem exists_tateIso_up (laws : Laws) {S : Scheme.{0}} (P : PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)) {K Ω : Type}
    [Field K] [Field Ω] [IsAlgClosed K] [IsAlgClosed Ω] [CharZero K] (i : K →+* Ω) {x : Sp K ⟶ S} {x' : Sp Ω ⟶ S}
    (u : Over.mk x' ⟶ Over.mk x) (hu : u.left = spMap i)
    (I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => WeilIs P.A P.L n y y' (unitOn c))) :
    ∃ I' : TateIso D Ω (Over.mk x' ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => WeilIs P.A P.L n y y' (unitOn c)),
      (∀ n, (I'.ζ n : Ω) = i (I.ζ n)) ∧ ∀ n v, I'.ev n v = u ≫ I.ev n v := by
  have : CharZero Ω := (RingHom.charZero_iff i.injective).1 ‹_›
  let f : (Over.mk x ⟶ P.A) →* (Over.mk x' ⟶ P.A) := MonoidHom.mk' (u ≫ ·) (MonObj.comp_mul u)
  have hinj : Function.Injective f := TorsionFieldExt.comp_injective u P.A
  have hu' : ∀ c : Kˣ, unitOn (Units.map i.toMonoidHom c) = Units.map u.left.appTop.hom.toMonoidHom (unitOn c) :=
    fun c => by
      rw [hu]
      exact Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i)))
  refine ⟨{ ζ := fun n => Units.map i.toMonoidHom (I.ζ n)
            ζ_prim := fun n hn => (I.ζ_prim n hn).map_of_injective (Units.map_injective i.injective)
            ζ_pow := fun n m hn hm => by rw [← map_pow, I.ζ_pow n m hn hm]
            ev := fun n v => f (I.ev n v)
            add := fun n a b => by rw [I.add, map_mul]
            lin := fun n c a => by rw [I.lin]; exact (Category.assoc u (I.ev n a) (act c)).symm
            ker := fun n hn a => by rw [← I.ker n hn a, map_eq_one_iff f hinj]
            onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
            tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm]
            isom := fun n hn a b => by
              rw [← map_zpow, hu']
              exact CommPairing.weilIs_pull laws.globalFns P.isAb P.isLB u (I.isom n hn a b) },
    fun _ => rfl, fun _ _ => rfl⟩
  · obtain ⟨y, hy, rfl⟩ := TorsionFieldExt.exists_of_isAlgClosed laws P u (Nat.cast_ne_zero.2 hn.ne')
      (Nat.cast_ne_zero.2 hn.ne') z hz
    obtain ⟨a, rfl⟩ := (I.onto n hn y).1 hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, (I.onto n hn _).2 ⟨a, rfl⟩, map_one]

theorem exists_eq_nsmul (l : Geo.Tor.Level H) {J J' : Ideal (𝓞 E)}
    (hJ : J * J' = Ideal.span {(l.M : 𝓞 E)}) {e : 𝓞 E} (he : e ∈ J) {a : D.La}
    (ha : a ∈ J' • (⊤ : Submodule (𝓞 E) D.La)) : ∃ c, e • a = l.M • c := by
  have h1 : e • a ∈ (J * J') • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul he ha
  rw [hJ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨c, -, hc⟩ := h1
  exact ⟨c, by rw [← hc, Nat.cast_smul_eq_nsmul]⟩

theorem exists_sab (laws : Laws) {K : Type} [Field K] (o : Full D K) :
    letI := H.starRing
    ∃ (PP : RigLB o.P.A) (_ : CubicalStr o.P.A PP), PP.L = o.P.L ∧ PP.IsSymmetric := by
  obtain ⟨rig, hrig⟩ := o.P.rigid
  let PP : RigLB o.P.A := ⟨o.P.L, rig, o.P.isLB, hrig⟩
  obtain ⟨cub⟩ := (laws.cube _ o.P PP rfl).1
  obtain ⟨U, hU, h⟩ := o.P.sym (default : PrimeSpectrum K)
  refine ⟨PP, cub, rfl, PrimNorm.isSymmetric_of_hasGen PP (hasGen_of_point o.P.A.hom hU (fun i => ?_) h)⟩
  fin_cases i
  · rfl
  · exact (Category.comp_id _).symm

theorem eta_smul {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (o : Obj D l b s) {e : 𝓞 E} (he : 1 - e ∈ l.Mb) (v : D.La) : o.eta (e • v) = o.eta v := by
  have h : v = e • v + (1 - e) • v := by rw [← add_smul, add_sub_cancel, one_smul]
  conv_rhs => rw [h]
  rw [o.eta_add, o.eta_ker _ (Submodule.smul_mem_smul he trivial), _root_.mul_one]

def IsFibre {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (ob : Obj D l b s) {K : Type} [Field K] (y : Sp K ⟶ S) (o : Full D K) : Prop :=
  letI := H.starRing
  ∃ φ : o.P.A.left ⟶ ob.t.G.left, IsGrpPullback o.P.A ob.t.G y φ ∧ LBIso o.P.L (ob.t.PP.L.pull φ) ∧
    (∀ x, (o.oa.act x).left ≫ φ = φ ≫ (ob.t.act.act x).left) ∧
    (∀ v, (o.I.ev l.A v).left ≫ φ = y ≫ (ob.etaA v).left) ∧
    ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), (o.I.ev l.M v).left ≫ φ = y ≫ (ob.eta v).left

theorem exists_obj (laws : Laws) (l : Geo.Tor.Level H) {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (o : Full D K)
    (b : Base l K) (hρ : b.ρ = o.ρ) (hζ : b.ζ = o.I.ζ l.A) :
    ∃ ob : Obj D l b (𝟙 (Sp K)), ∀ {B : Type} [CommRing B] {b' : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
      (ob' : Obj D l b' s) (y : Sp K ⟶ S), Nonempty (ObjMap ob ob' y) ↔ IsFibre ob' y o := by
  letI := H.starRing
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨⟨L, rig, hL, hrig⟩, cub, rfl, sym⟩ := exists_sab laws o
  obtain ⟨f, hf, e, he, hfe⟩ : ∃ f ∈ l.Mb, ∃ e ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), f + e = 1 :=
    Submodule.mem_sup.1 (by rw [l.coprime]; trivial)
  have h2 : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      o.I.ev l.M a = o.I.ev l.M (e • a) := fun a ha => by
    obtain ⟨c, hc⟩ := exists_eq_nsmul l l.prod hf ha
    have h1 : a = e • a + l.M • c := by rw [← hc, ← add_smul, add_comm, hfe, one_smul]
    conv_lhs => rw [h1]
    rw [o.I.add, (o.I.ker _ hM _).2 ⟨c, rfl⟩, _root_.mul_one]
  let t : SAB H (Sp K) :=
    { G := o.P.A, semi := isSemiAbelian_of_isAbelianScheme _ o.P.isAb, act := ofRingAct o.oa.toRingAct
      PP := ⟨o.P.L, rig, hL, hrig⟩, cub := cub, sym := sym
      adj := fun a => lbIso_of_rosatiAdj o.P.isLB (o.oa.rosati a), prim := o.prim }
  refine ⟨{ t := t, proper := o.P.isAb.proper, ample := o.P.ample, ktriv := o.P.ktriv
            eta := fun a => o.I.ev l.M (e • a)
            eta_add := fun a c => by rw [smul_add]; exact o.I.add _ _ _
            eta_ker := fun a ha => (o.I.ker _ hM _).2
              (exists_eq_nsmul l (by rw [mul_comm]; exact l.prod) he ha)
            etaA := o.I.ev l.A
            etaA_add := o.I.add _
            etaA_ker := fun a => (o.I.ker _ l.A_pos _).2 ⟨a, rfl⟩
            geom := ?_ }, fun ob' y => ⟨?_, ?_⟩⟩
  · intro k _ _ x β hx
    obtain rfl : x = spMap β := (Category.comp_id x).symm.trans hx
    have := o.P.isAb.smooth
    refine ⟨by rw [hρ]; exact LieExt.detCond_extend D β o.P.A _ o.det, ?_⟩
    obtain ⟨I', hζ', hev⟩ := exists_tateIso_up laws o.P o.oa.act β (x := 𝟙 _) (x' := spMap β) (toUnit _)
      (ObjPull.toUnit_left' _) o.I
    refine ⟨I', by rw [hζ', hζ], fun a => (hev _ _).symm, fun a ha => Eq.trans ?_ (hev _ _).symm⟩
    rw [h2 a ha]
  · rintro ⟨m⟩
    obtain ⟨w, hw, -⟩ := m.lin
    refine ⟨m.cm.F, m.cart, ⟨w, hw⟩, m.act, m.etaA, fun v hv => ?_⟩
    rw [h2 v hv]
    exact m.eta v
  · rintro ⟨φ, h₁, h₂, h₃, h₄, h₅⟩
    obtain ⟨m, rfl⟩ := exists_sabMap_of_isProper_of_lbIso laws.globalFns E H _ _ ob'.t t y φ ob'.proper h₁ h₂ h₃
    refine ⟨⟨m, fun v => ?_, h₄⟩⟩
    rw [← eta_smul ob' (e := e) (by rw [← hfe, add_sub_cancel_right]; exact hf) v]
    exact h₅ _ (Submodule.smul_mem_smul he trivial)

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem exists_isFibre {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (ob : Obj D l b s) {K : Type} [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) :
    ∃ o : Full D K, IsFibre ob y o ∧
      ∀ f : B →+* K, y ≫ s = spMap f → o.ρ = f b.ρ ∧ (o.I.ζ l.A : K) = f b.ζ := by
  letI := H.starRing
  obtain ⟨o', ⟨m⟩⟩ := ObjPull.objPull_of_pol (PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally)
    E H D l B B b b (RingHom.id B) S (Sp K) s (y ≫ s) y rfl rfl
    (by rw [show spMap (RingHom.id B) = 𝟙 _ from Spec.map_id _, Category.comp_id]) ob
  let β : B →+* K := (Spec.preimage (y ≫ s)).hom
  obtain ⟨hdet, I, hI, hA, hM⟩ := o'.geom K (𝟙 _) β ((Category.id_comp _).trans (Spec.map_preimage (y ≫ s)).symm)
  obtain ⟨w, hw, -⟩ := m.lin
  have u : (toUnit (Over.mk (𝟙 (Sp K)))).left = 𝟙 _ := ObjPull.toUnit_left' _
  refine ⟨{ P := Obj.toPolAV o', oa := ⟨o'.t.act.toRingAct, o'.t.rosatiAdj⟩, prim := o'.t.prim, ρ := β b.ρ
            ρ_sq := by rw [← map_pow, b.ρ_sq, map_neg, map_natCast]
            det := hdet, I := I, closed := ‹_› },
    ⟨m.cm.F, m.cart, ⟨w, hw⟩, m.act, fun v => ?_, fun v hv => ?_⟩, fun f hf => ?_⟩
  · refine Eq.trans (congrArg (fun q => q.left ≫ m.cm.F) (hA v)).symm ?_
    rw [Over.comp_left, u]
    exact (congrArg (· ≫ m.cm.F) (Category.id_comp _)).trans (m.etaA v)
  · refine Eq.trans (congrArg (fun q => q.left ≫ m.cm.F) (hM v hv)).symm ?_
    rw [Over.comp_left, u]
    exact (congrArg (· ≫ m.cm.F) (Category.id_comp _)).trans (m.eta v)
  · obtain rfl : β = f := spMap_inj ((Spec.map_preimage (y ≫ s)).trans hf)
    exact ⟨rfl, hI⟩

theorem IsFibre.ext {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    {ob : Obj D l b s} {K K' : Type} [Field K] [Field K'] (f : K →+* K') {y : Sp K ⟶ S} {o : Full D K}
    {o' : Full D K'} (h : IsFibre ob y o) (ψ : o'.P.A.left ⟶ o.P.A.left)
    (g₁ : IsGrpPullback o'.P.A o.P.A (spMap f) ψ) (g₂ : LBIso o'.P.L (o.P.L.pull ψ))
    (g₃ : letI := H.starRing; ∀ x, (o'.oa.act x).left ≫ ψ = ψ ≫ (o.oa.act x).left)
    (g₄ : ∀ n v, 0 < n → (o'.I.ev n v).left ≫ ψ = spMap f ≫ (o.I.ev n v).left) : IsFibre ob (spMap f ≫ y) o' := by
  obtain ⟨φ, h₁, h₂, h₃, h₄, h₅⟩ := h
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  refine ⟨ψ ≫ φ, g₁.comp h₁, LBIso.trans o'.P.isLB (pull_isLB o.P.isLB _) (pull_isLB ob.t.PP.isLB _) g₂
    (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
      (chartPullSame ob.t.PP.L (fun _ : PUnit => ψ ≫ φ) (fun _ => φ) (fun _ => 1) ψ fun _ => rfl) h₂),
    fun x => ?_, fun v => ?_, fun v hv => ?_⟩
  · rw [← Category.assoc, g₃, Category.assoc, h₃, Category.assoc]
  · refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) (g₄ _ v l.A_pos))).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (h₄ v)).trans (Category.assoc _ _ _).symm)
  · refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) (g₄ _ v hM))).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (h₅ v hv)).trans (Category.assoc _ _ _).symm)

theorem existsUnique_point (laws : Laws) {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {K : Type} [Field K] [IsAlgClosed K] (bF : c.F →+* K) (o : Full D K)
    (hρ : ∀ r : c.F, (r : ℂ) = H.rt0 → o.ρ = bF r) (hζ : ∀ z : c.F, (z : ℂ) = zeta l.A → (o.I.ζ l.A : K) = bF z) :
    ∃! y : Sp K ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap bF ∧ IsFibre Y.oF y o := by
  have : CharZero K := (RingHom.charZero_iff bF.injective).1 inferInstance
  let b : Base l K :=
    { unit := fun n hn => IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne'), ρ := o.ρ, ρ_sq := o.ρ_sq, ζ := o.I.ζ l.A
      ζ_prim := (o.I.ζ_prim _ l.A_pos).map_of_injective (f := Units.coeHom K) Units.val_injective }
  obtain ⟨ob, hob⟩ := exists_obj laws l o b rfl rfl
  let i : KA l →+* c.F := (IntermediateField.inclusion c.le).toRingHom
  obtain ⟨f, ⟨hf, ⟨m⟩⟩, hu⟩ := moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo K b (bF.comp i) (Sp K) (𝟙 _) ob
    inferInstance (hρ _ rfl).symm (hζ _ rfl).symm
  rw [Category.id_comp, spMap_comp] at hf
  let y : Sp K ⟶ Xo.XF c := pullback.lift f (spMap bF) hf
  have hy : y ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  refine ⟨y, ⟨pullback.lift_snd _ _ _, (hob _ _).1 ?_⟩, fun y' ⟨h₁, h₂⟩ => ?_⟩
  · rw [← hy] at m
    obtain ⟨m', -⟩ := ObjComp.objMap_cancel Y.m0 m
    exact ⟨m'⟩
  · obtain ⟨m'⟩ := (hob _ _).2 h₂
    obtain ⟨m'', -⟩ := ObjComp.objMap_comp Y.m0 m'
    refine pullback.hom_ext ((hu _ ⟨?_, ⟨m''⟩⟩).trans hy.symm) (h₁.trans (pullback.lift_snd _ _ _).symm)
    rw [Category.id_comp, spMap_comp, Category.assoc, pullback.condition, ← Category.assoc, h₁]

end GlobalTheory.FullPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormalStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_section_extends_normal : ∀ (Z : Scheme.{0}) [CompactSpace Z] [QuasiSeparatedSpace Z] (AA : LB Z), AA.IsLB → (∀ z : Z, ∃ (d : ℕ) (s : H0 AA d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (x : Sp (FractionRing R) ⟶ Z) (e : LB.Gen (AA.pull x)), e.IsGen → (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (φ : R →+* W) (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) → ∃ χ : Sp W ⟶ Z, spMap gam ≫ x = jK W ≫ χ ∧ ∃ e' : LB.Gen (AA.pull χ), e'.IsGen ∧ ∀ z J, Good AA z J → val (L := AA) (φ := fun _ : PUnit => x) (ε := fun _ => 1) e (spMap gam) z J = val (L := AA) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (jK W) z J) → ∃ χ : Sp R ⟶ Z, jK R ≫ χ = x := by
  first | exact @GlobalTheory.ExtLB.exists_extension | exact GlobalTheory.ExtLB.exists_extension | (intros; apply GlobalTheory.ExtLB.exists_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIntegralRatios
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatioExt

open GlobalTheory.SecRingIso GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem corresp_refl {X Z : Scheme.{0}} {L : LB X} {φ ψ : Z ⟶ X}
    (hc : ∀ N : ℕ, 4 ≤ N → ∀ x : X, ∃ s : H0 L N, x ∈ nonzeroLocus s)
    (h : ∀ n : ℕ, 1 ≤ n → ∀ (a b : H0 L n) (z : Z) (j j' : Fin 1 → L.ι), φ z ∈ ch L j → ψ z ∈ ch L j' →
      sv φ z a j * sv ψ z b j' = sv φ z b j * sv ψ z a j') :
    Corresp (L := L) (L' := L) (fun _ _ => Equiv.refl _) φ ψ := by
  intro n hn a b z
  refine ⟨?_, fun j j' _ hj hj' => h n hn a b z j j' hj hj'⟩
  have hk : 1 ≤ n * (3 + 1) := by omega
  obtain ⟨d, hd, -⟩ := presMul_refl.exists_pow hn b 3 _ hk rfl
  obtain ⟨c, hcφ⟩ := hc (n * (3 + 1)) (by omega) (φ z)
  obtain ⟨c', hcψ⟩ := hc (n * (3 + 1)) (by omega) (ψ z)
  obtain ⟨j, hj⟩ := exists_ch hcφ
  obtain ⟨j', hj'⟩ := exists_ch hcψ
  show φ z ∈ nonzeroLocus b ↔ ψ z ∈ nonzeroLocus b
  rw [mem_iff b φ z hj, mem_iff b ψ z hj']
  constructor
  · intro hb
    have e := h _ hk d c' z j j' hj hj'
    rw [sv_pow hd φ z hj, sv_pow hd ψ z hj'] at e
    have u := (hb.pow (3 + 1)).mul ((mem_iff c' ψ z hj').1 hcψ)
    rw [e] at u
    exact isUnit_pow_succ_iff.1 (isUnit_of_mul_isUnit_right u)
  · intro hb
    have e := h _ hk c d z j j' hj hj'
    rw [sv_pow hd φ z hj, sv_pow hd ψ z hj'] at e
    have u := ((mem_iff c φ z hj).1 hcφ).mul (hb.pow (3 + 1))
    rw [e] at u
    exact isUnit_pow_succ_iff.1 (isUnit_of_mul_isUnit_left u)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G]

theorem exists_integral (U : Unif I D A G)
    {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))} (hw : w.IsGen)
    {n : ℕ} (hn : 1 ≤ n) (a : H0 A.L n) : ∃ (r : R) (σ : H0 U.LG.L n), r ≠ 0 ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ ((Over.pullback (jK R)).obj G).left) (z : Z) (i : U.LG.L.ι) (j : A.L.ι),
        (f ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i → (f ≫ U.gen.hom.left) z ∈ A.L.U j →
        powVal σ (f ≫ pullback.fst G.hom (jK R)) z i =
          cst ((f ≫ pullback.snd G.hom (jK R)) ≫ jK R) z r *
            ((isoVal w f z i j ^ (n : ℤ)).val * powVal a (f ≫ U.gen.hom.left) z j) := by
  obtain ⟨s, hs⟩ := exists_move A.isLB U.LG.isLB hw (𝟙 _) (n : ℤ) (g₁ := 𝟙 A.A.left) U.gen.hom.left
    ((Category.comp_id _).trans (Category.id_comp _).symm) (g₂ := pullback.fst G.hom (jK R))
    (Category.id_comp _).symm a
  obtain ⟨F, ⟨r, hr, σ, -, h₁, -⟩, -⟩ := (U.expand n hn).1 s
  refine ⟨r, σ, hr, fun Z f z i j hi hj => ?_⟩
  obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB z (fun _ : Unit => f ≫ pullback.fst G.hom (jK R))
    (fun _ => i) (fun _ _ _ => rfl) (fun _ => hi)
  have e₁ := ExpInt.secScal_sval h₁ f z hJ
  rw [sval_eq_powVal, sval_eq_powVal, Category.comp_id, e (), ExpInt.gs_scal, hs Z f z i j hi hj,
    Category.comp_id, ← Category.assoc] at e₁
  exact e₁

end GlobalTheory.RatioExt

namespace GlobalTheory

open GlobalTheory.SecRingIso GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RatioExt in

theorem hom_ext_of_integral_ratios : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (P : ∀ k : ℕ, H0 U.LG.L k → Prop), (∀ k : ℕ, 1 ≤ k → ∀ σ₀ : H0 U.LG.L k, ∃ (c : R) (σ : H0 U.LG.L k), c ≠ 0 ∧ (∀ i, σ.f i = resTop _ (scal G.hom c) * σ₀.f i) ∧ P k σ) → ∀ (Z : Scheme.{0}) (f₁ f₂ : Z ⟶ ((Over.pullback (jK R)).obj G).left), f₁ ≫ pullback.snd G.hom (jK R) = f₂ ≫ pullback.snd G.hom (jK R) → (∀ z : Z, ∃ i₁ i₂ : U.LG.L.ι, (f₁ ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i₁ ∧ (f₂ ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i₂ ∧ ∀ k : ℕ, 1 ≤ k → ∀ σ τ : H0 U.LG.L k, P k σ → P k τ → gs (f₁ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₁)) (σ.f (fun _ => i₁)) * gs (f₂ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₂)) (τ.f (fun _ => i₂)) = gs (f₁ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₁)) (τ.f (fun _ => i₁)) * gs (f₂ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₂)) (σ.f (fun _ => i₂))) → f₁ = f₂ := by
  intro hL R _ _ I D A G _ _ U P hP Z f₁ f₂ hK h
  obtain ⟨w, hw⟩ := U.ext
  have key : ∀ n : ℕ, 1 ≤ n → ∀ a : H0 A.L n, ∃ (r : R) (σ : H0 U.LG.L n), r ≠ 0 ∧ P n σ ∧
      ∀ (f : Z ⟶ ((Over.pullback (jK R)).obj G).left) (z : Z) (i : U.LG.L.ι) (j : Fin 1 → A.L.ι),
        (f ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i → (f ≫ U.gen.hom.left) z ∈ ch A.L j →
        powVal σ (f ≫ pullback.fst G.hom (jK R)) z i =
          cst ((f ≫ pullback.snd G.hom (jK R)) ≫ jK R) z r *
            ((isoVal w f z i (j 0) ^ (n : ℤ)).val * sv (f ≫ U.gen.hom.left) z a j) := fun n hn a => by
    obtain ⟨r, σ₀, hr, H⟩ := exists_integral U hw hn a
    obtain ⟨c, σ, hc, hσ, hPσ⟩ := hP n hn σ₀
    refine ⟨c * r, σ, mul_ne_zero hc hr, hPσ, fun f z i j hi hj => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun t => congrArg j (Subsingleton.elim _ _)⟩
    have e₁ := H Z f z i j hi (mem_wchart.1 hj 0)
    have e₂ : powVal σ (f ≫ pullback.fst G.hom (jK R)) z i = cst ((f ≫ pullback.fst G.hom (jK R)) ≫ G.hom) z c *
        powVal σ₀ (f ≫ pullback.fst G.hom (jK R)) z i :=
      secIsMul_gs (p := G.hom) (a := c) hσ _ z _ (mem_wchart.2 fun _ => hi)
    rw [Category.assoc, pullback.condition, ← Category.assoc] at e₂
    rw [e₂, e₁, H1.cst_mul, _root_.mul_assoc]
    rfl
  have := A.isAb.proper
  have : CompactSpace A.A.left := QuasiCompact.compactSpace_of_compactSpace A.A.hom
  have : QuasiSeparatedSpace A.A.left := quasiSeparatedSpace_of_quasiSeparated A.A.hom
  have hc := fun N hN => (polAV_nonzeroLocus_cover_affine hL.ample A (N := N) hN).1
  have h₁ : Corresp (L := A.L) (L' := A.L) (fun _ _ => Equiv.refl _) (f₁ ≫ U.gen.hom.left) (f₂ ≫ U.gen.hom.left) := by
    refine corresp_refl hc fun n hn a b z j j' hj hj' => ?_
    obtain ⟨i₁, i₂, m₁, m₂, H⟩ := h z
    obtain ⟨r, σ, hr, hσ, Hσ⟩ := key n hn a
    obtain ⟨s, τ, hs, hτ, Hτ⟩ := key n hn b
    have e : powVal σ (f₁ ≫ pullback.fst G.hom (jK R)) z i₁ * powVal τ (f₂ ≫ pullback.fst G.hom (jK R)) z i₂ =
        powVal τ (f₁ ≫ pullback.fst G.hom (jK R)) z i₁ * powVal σ (f₂ ≫ pullback.fst G.hom (jK R)) z i₂ :=
      H n hn σ τ hσ hτ
    rw [Hσ f₁ z i₁ j m₁ hj, Hσ f₂ z i₂ j' m₂ hj', Hτ f₁ z i₁ j m₁ hj, Hτ f₂ z i₂ j' m₂ hj', hK] at e
    refine ((((ExpInt.isUnit_cst (f₂ ≫ pullback.snd G.hom (jK R)) z hr).mul
      (ExpInt.isUnit_cst (f₂ ≫ pullback.snd G.hom (jK R)) z hs)).mul
      (isoVal w f₁ z i₁ (j 0) ^ (n : ℤ)).isUnit).mul (isoVal w f₂ z i₂ (j' 0) ^ (n : ℤ)).isUnit).mul_left_cancel ?_
    linear_combination e
  have h₂ : Corresp (L := A.L) (L' := A.L) (fun _ _ => Equiv.refl _) (f₂ ≫ U.gen.hom.left) (f₂ ≫ U.gen.hom.left) :=
    corresp_refl hc fun n hn a b z j j' hj hj' => by
      refine (congrArg₂ (· * ·) (sec_trans a _ z hj hj') rfl).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) (sec_trans b _ z hj hj') rfl).symm)
      exact (mul_right_comm _ _ _)
  have e := h₁.unique A.isLB h₂ (n := 4) (by norm_num) id
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (hc 4 le_rfl x))
    (polAV_nonzeroLocus_cover_affine hL.ample A le_rfl).2
  have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
  exact (cancel_mono _).1 e

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineOpenOfLocalSectionCombinationLocusStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_of_local_sectionCombination_locus : ∀ (P Z : Scheme.{0}) (π : P ⟶ Z) [IsProper π] (J : Type) [Fintype J] (D : P.Opens) (W : Z.Opens), IsAffineOpen W → D ≤ π ⁻¹ᵁ W → (∀ z ∈ W, ∃ (W' : Z.Opens) (H : LB (π ⁻¹ᵁ W').toScheme) (σ : J → H.Sec) (m : J → Γ(Z, W ⊓ W')), z ∈ W' ∧ IsAffineOpen W' ∧ ⨆ k, nonzeroLocus (σ k) = ⊤ ∧ (∀ k, IsAffineOpen (nonzeroLocus (σ k))) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ (π ⁻¹ᵁ W').toScheme) (w : J → K), ⊤ ≤ (y ≫ (π ⁻¹ᵁ W').ι ≫ π) ⁻¹ᵁ W → Crd H σ y w → (⊤ ≤ (y ≫ (π ⁻¹ᵁ W').ι) ⁻¹ᵁ D ↔ ∑ k, valR (y ≫ (π ⁻¹ᵁ W').ι ≫ π) (W ⊓ W') (m k) * w k ≠ 0)) → IsAffineOpen D := by
  first | exact @GlobalTheory.ZH.CombLocus.isAffineOpen_of_comb | exact GlobalTheory.ZH.CombLocus.isAffineOpen_of_comb | (intros; apply GlobalTheory.ZH.CombLocus.isAffineOpen_of_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionTestSpecialFibreOpenPartStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_testSpecialFibre_openPart : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ (f' : t.u.G.left ⟶ Q.G.toScheme), f' ≫ Q.G.ι = tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι → ∀ h : pullback t.u.G.hom (rPt p ≫ spMap t.u.j) ⟶ pullback (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y), h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f' → h ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion h := by
  first | exact @GlobalTheory.ZH.FibreImm.isClosedImmersion_special_fibre | exact GlobalTheory.ZH.FibreImm.isClosedImmersion_special_fibre | (intros; apply GlobalTheory.ZH.FibreImm.isClosedImmersion_special_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosedStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_powerSeries_arcs_over_algClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Over (Sp k)) [IsIntegral X.left], IsSeparated X.hom → LocallyOfFiniteType X.hom → QuasiCompact X.hom → (∀ a : Sp (FractionRing (PowerSeries k)) ⟶ X.left, a ≫ X.hom = spMap (algebraMap k (FractionRing (PowerSeries k))) → ∃ b : Sp (PowerSeries k) ⟶ X.left, spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a) → IsProper X.hom := by
  first | exact @GlobalTheory.ArcProper.isProper_of_arcs | exact GlobalTheory.ArcProper.isProper_of_arcs | (intros; apply GlobalTheory.ArcProper.isProper_of_arcs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyFormalUniformisationTowerStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_formalUniformisationTower : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → IsProper (pullback.snd G.hom (jK R)) → SplitOver G I → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X), Nonempty (TowerR I P X) := by
  first | exact @GlobalTheory.FormalTower.nonempty_towerR | exact GlobalTheory.FormalTower.nonempty_towerR | (intros; apply GlobalTheory.FormalTower.nonempty_towerR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLawOfHasTestsOfIndep
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.nonempty_law_of_hasTests_of_indep :
    ∀ C : Core, C.HasTests → C.Indep → Nonempty C.Law := by
  intro C hT hI
  have hF : C.Fib := GlobalTheory.T.fibre_eq_specialFibre_of_reduction_indep C hI
  have hS := GlobalTheory.T.smoothOfRelativeDimension_groupScheme_of_tests C hT hF
  have hC : C.TestCart := GlobalTheory.T.testCart_of_specialFibre_surjective C hF hS
  have hL : C.FibLaw := GlobalTheory.T.fibreLaw_of_testCartesian C hC
  exact GlobalTheory.T.nonempty_law_abelianSchemeProperClosure C hS hC (GlobalTheory.T.exists_mul_of_isSquare_of_fibLaw C hT hS hC hL) (GlobalTheory.T.exists_inverse_extension_properClosure C hT hS hC hL)

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyTestModelToClosureStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_testModel_to_closure : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u), S.Big → Nonempty (Q.TMap t c) := by
  first | exact @GlobalTheory.ZH.TestMap.nonempty_tMap | exact GlobalTheory.ZH.TestMap.nonempty_tMap | (intros; apply GlobalTheory.ZH.TestMap.nonempty_tMap <;> assumption)
end

