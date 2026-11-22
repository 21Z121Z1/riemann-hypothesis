import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1297
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0060
import GroundTheory.GlobalFields.Adele.Compact

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.ExistsOpenAvoid
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.PNbhd2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem exists_open_avoid (w : Plc E) (x : GLw n w) (hx : x ≠ 1) :
    ∃ V : Subgroup (GLw n w), IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w n ∧ x ∉ V := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  by_cases hxK : x ∈ GlobalTheory.LFun.KGL w n
  swap
  · exact ⟨_, hKo, le_rfl, hxK⟩
  have hne : ∃ i j, x.val i j ≠ (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
    by_contra h
    push_neg at h
    exact hx (Units.ext (Matrix.ext h))
  obtain ⟨i, j, hij⟩ := hne
  haveI : CompactSpace ↥(GlobalTheory.LFun.KGL w n) := isCompact_iff_compactSpace.1 hKc
  let f : ↥(GlobalTheory.LFun.KGL w n) → w.adicCompletion E :=
    fun g => g.1.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j
  have hf : Continuous f :=
    Continuous.sub (Continuous.matrix_elem (Units.continuous_val.comp continuous_subtype_val) i j) continuous_const
  obtain ⟨A, hA⟩ := NonarchimedeanAddGroup.is_nonarchimedean
    ({x.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j}ᶜ : Set (w.adicCompletion E))
    (isOpen_compl_singleton.mem_nhds (by simpa using (sub_ne_zero.2 hij).symm))
  have hW : IsClopen (f ⁻¹' (A : Set (w.adicCompletion E))) := A.isClopen.preimage hf
  have h1 : (1 : ↥(GlobalTheory.LFun.KGL w n)) ∈ f ⁻¹' (A : Set (w.adicCompletion E)) := by
    simp [f, A.zero_mem]
  obtain ⟨H, hH⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hW h1
  refine ⟨(H : Subgroup _).map (GlobalTheory.LFun.KGL w n).subtype, ?_, Subgroup.map_subtype_le _, ?_⟩
  · exact hKo.isOpenEmbedding_subtypeVal.isOpenMap _ H.isOpen
  · rintro ⟨h, hh, rfl⟩
    exact hA (hH hh) rfl

private theorem exists_Kw
    (F : Finset (Σ w : Plc E, {V : Subgroup (GLw n w) // IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w n})) :
    ∃ Kw : ∀ w : Plc E, Subgroup (GLw n w), (∀ w, IsOpen (Kw w : Set (GLw n w)) ∧ Kw w ≤ GlobalTheory.LFun.KGL w n) ∧
      ∀ i ∈ F, Kw i.1 ≤ i.2.1 := by
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨fun w => GlobalTheory.LFun.KGL w n,
      fun w => ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).1, le_rfl⟩, by simp⟩
  | insert i F _ ih =>
    obtain ⟨Kw, h1, h2⟩ := ih
    obtain ⟨v, V, hVo, hVK⟩ := i
    have hle : ∀ w, Function.update Kw v (Kw v ⊓ V) w ≤ Kw w := fun w => by
      by_cases h : w = v
      · subst h
        rw [Function.update_self]
        exact inf_le_left
      · rw [Function.update_of_ne h]
    refine ⟨Function.update Kw v (Kw v ⊓ V), fun w => ?_, fun j hj => ?_⟩
    · refine ⟨?_, (hle w).trans (h1 w).2⟩
      by_cases h : w = v
      · subst h
        rw [Function.update_self]
        exact (h1 w).1.inter hVo
      · rw [Function.update_of_ne h]
        exact (h1 w).1
    · rcases Finset.mem_insert.1 hj with rfl | hj
      · simp only [Function.update_self]
        exact inf_le_right
      · exact (hle j.1).trans (h2 j hj)

end UpperTheory.Gal.CertificateRingHomMap.PNbhd2

theorem UpperTheory.Gal.CertificateRingHomMap.pNbhd2_of :
    UpperTheory.Gal.CertificateRingHomMap.Nbhd2 := by
  intro E _ _ _ n O hO
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  let p : finU E n →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU E n).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hfin : ∀ x : UA E n, x ∈ finU E n ↔
      finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n) := by
    intro x
    constructor
    · intro hx
      have h1 : GeneralLinearGroup.map (pInf E) (x : GA E n) = 1 := hx
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
    · intro hx
      change GeneralLinearGroup.map (pInf E) (x : GA E n) = 1
      rw [← hx, pInf_finGL]
  have hc : IsClosed ((finU E n : Subgroup (UA E n)) : Set (UA E n)) := by
    have e : ((finU E n : Subgroup (UA E n)) : Set (UA E n)) =
        {x : UA E n | finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n)} :=
      Set.ext hfin
    rw [e]
    exact isClosed_eq (GlobalTheory.DefU.LocAdm.continuous_finGL.comp (continuous_map_pFin.comp continuous_subtype_val))
      continuous_subtype_val
  have hι : Topology.IsClosedEmbedding (fun x : finU E n => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hc.isClosedEmbedding_subtypeVal
  have hKc := GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)
  have hKo := GlobalTheory.EulerTwRestr.isOpen_Kglob (E := E) (n := n)
  have hC : IsCompact {u : finU E n | p u ∈ GlobalTheory.EulerTw.Kglob E n} :=
    IsCompact.of_isClosed_subset (hι.isCompact_preimage (hKc.image GlobalTheory.DefU.LocAdm.continuous_finGL))
      ((Subgroup.isClosed_of_isOpen _ hKo).preimage hp) fun x hx => ⟨p x, hx, (hfin x).1 x.2⟩
  have hL : ∀ w : Plc E, Continuous fun u : finU E n => cLoc w u.1 := fun w =>
    (show Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E w)) from
      Continuous.units_map _ (Continuous.matrix_map continuous_id
        (show Continuous (pLoc E w) from RestrictedProduct.continuous_eval
          (R := fun w : Plc E => w.adicCompletion E)
          (A := fun w : Plc E => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) w))).comp hp
  let D : (Σ w : Plc E, {V : Subgroup (GLw n w) // IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w n}) →
      Set (finU E n) := fun i => {u | cLoc i.1 u.1 ∈ i.2.1}
  have hD : ∀ i, IsClosed (D i) := fun i => (Subgroup.isClosed_of_isOpen _ i.2.2.1).preimage (hL i.1)
  have hone : ∀ u : finU E n, (∀ i, u ∈ D i) → u = 1 := by
    intro u hu
    have h1 : ∀ w : Plc E, cLoc w u.1 = 1 := by
      intro w
      by_contra hne
      obtain ⟨V, hVo, hVK, hV⟩ := UpperTheory.Gal.CertificateRingHomMap.PNbhd2.exists_open_avoid w _ hne
      exact hV (hu ⟨w, V, hVo, hVK⟩)
    have h2 : p u = 1 := GlobalTheory.EulerTwRestr.gl_ext fun w => (h1 w).trans (map_one _).symm
    have h3 : GeneralLinearGroup.map (pInf E) (u.1 : GA E n) = 1 := u.2
    exact Subtype.ext (Subtype.ext (ga_ext (by rw [h3]; simp) (by simpa using (show GeneralLinearGroup.map (pFin E) (u.1 : GA E n) = 1 from h2))))
  have hemp : ({u : finU E n | p u ∈ GlobalTheory.EulerTw.Kglob E n} \ (O : Set (finU E n))) ∩ ⋂ i, D i = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun u hu => ?_
    have := hone u (Set.mem_iInter.1 hu.2)
    exact hu.1.2 (this ▸ O.one_mem)
  obtain ⟨F, hF⟩ := (hC.diff hO).elim_finite_subfamily_closed D hD hemp
  obtain ⟨Kw, hK1, hK2⟩ := UpperTheory.Gal.CertificateRingHomMap.PNbhd2.exists_Kw F
  refine ⟨F.image Sigma.fst, Kw, hK1, fun u hu hS => ?_⟩
  by_contra huO
  have hmem : u ∈ ({u : finU E n | p u ∈ GlobalTheory.EulerTw.Kglob E n} \ (O : Set (finU E n))) ∩ ⋂ i ∈ F, D i :=
    ⟨⟨GlobalTheory.EulerTwRestr.mem_Kglob.2 hu, huO⟩,
      Set.mem_iInter₂.2 fun i hi => hK2 i hi (hS i.1 (Finset.mem_image_of_mem _ hi))⟩
  rw [hF] at hmem
  exact hmem
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.InvTMemSim
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

theorem invT_val {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : (invT n R g).val = (g⁻¹).valᵀ := rfl

@[simp] theorem invT_invT' {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : invT n R (invT n R g) = g := by
  apply Units.ext
  rw [invT_val, ← map_inv, invT_val, inv_inv, transpose_transpose]

theorem invT_mem_Sim {A B : Type} [CommRing A] [CommRing B] {σ : A →+* A} {i : B →+* A} {n : ℕ} {p : GL (Fin n) A × Bˣ}
    (h : p ∈ Sim σ i n) : (invT n A p.1, p.2⁻¹) ∈ Sim σ i n := by
  have h1 := mem_Sim.1 h
  have h2 : p.1.valᵀ * p.1.val.map σ = i p.2 • (1 : Matrix (Fin n) (Fin n) A) := by
    have := congrArg transpose h1
    rwa [transpose_mul, transpose_transpose, transpose_smul, transpose_one] at this
  have h3 : i (p.2⁻¹ : Bˣ) * i p.2 = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have h4 : (p.1⁻¹).valᵀ * p.1.valᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  have h5 : (p.1⁻¹).val.map σ * p.1.val.map σ = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have h6 : p.1.val.map σ = i p.2 • (p.1⁻¹).valᵀ := by
    rw [← Matrix.one_mul (p.1.val.map σ), ← h4, Matrix.mul_assoc, h2, Matrix.mul_smul, Matrix.mul_one]
  refine mem_Sim.2 ?_
  show (((p.1⁻¹).valᵀ).map σ)ᵀ * (p.1⁻¹).valᵀ = i (p.2⁻¹ : Bˣ) • 1
  rw [transpose_map, transpose_transpose, ← h5, h6, Matrix.mul_smul, smul_smul, h3, one_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def th : GUf E n →* GUf E n :=
  (((invT n (Af E)).prodMap invMonoidHom).comp (GUf E n).subtype).codRestrict _ fun g => invT_mem_Sim g.2

def th0 : Gam0 E n →* Gam0 E n :=
  (((invT n E).prodMap invMonoidHom).comp (Gam0 E n).subtype).codRestrict _ fun g =>
    ⟨invT_mem_Sim g.2.1, (Units.posSubgroup ℚ).inv_mem g.2.2⟩

@[simp] theorem sim_th (g : GUf E n) : sim (th g) = (sim g)⁻¹ := rfl

@[simp] theorem mat_th (g : GUf E n) : mat (th g) = invT n _ (mat g) := rfl

@[simp] theorem comp_th (w : Plc E) (g : GUf E n) : comp w (th g) = invT n _ (comp w g) := GlobalTheory.SplitPts.invT_map _ _

@[simp] theorem th_th (g : GUf E n) : th (th g) = g := Subtype.ext (Prod.ext (invT_invT' _) (inv_inv _))

theorem th_rat (γ : Gam0 E n) : th (rat γ) = rat (th0 γ) :=
  Subtype.ext (Prod.ext (GlobalTheory.SplitPts.invT_map _ _).symm (map_inv (Units.map (algebraMap ℚ AfQ).toMonoidHom) _).symm)

theorem guf_ext {g g' : GUf E n} (h1 : sim g = sim g') (h2 : ∀ w, comp w g = comp w g') : g = g' :=
  Subtype.ext (Prod.ext (Units.ext (GlobalTheory.SplitPts.matAf_ext fun w => congrArg Units.val (h2 w))) h1)

theorem invT_mem_KGL {w : Plc E} {y : GLw n w} (h : y ∈ KGL w n) : invT n _ y ∈ KGL w n := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨invT n _ z, GlobalTheory.SplitPts.invT_map _ z⟩

def levT (Kw : ∀ w : Plc E, Subgroup (GLw n w)) : ∀ w : Plc E, Subgroup (GLw n w) := fun w => (Kw w).comap (invT n _)

theorem th_mem_lev {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} {k : GUf E n} :
    th k ∈ lev S Kw ↔ k ∈ lev S (levT Kw) := by
  simp only [mem_lev, sim_th, comp_th, inv_mem_iff, levT, Subgroup.mem_comap]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₃_congr fun w _ _ => ⟨fun h => ?_, invT_mem_KGL⟩
  simpa using invT_mem_KGL h

def embBar (E : Type) [Field E] (n : ℕ) : GL (Fin n) E →* (InfinitePlace E → GL (Fin n) ℂ) :=
  MonoidHom.pi fun v => GeneralLinearGroup.map (ComplexEmbedding.conjugate v.embedding)

def xiG (W : Wt E n) (c : InfinitePlace E → ℤ) : Representation ℂ (GL (Fin n) E × ℚˣ) (Module.Dual ℂ W.Sp) where
  toFun p := (∏ v : InfinitePlace E, (v.embedding p.1.val.det * ComplexEmbedding.conjugate v.embedding p.1.val.det) ^ (-c v)) •
    Representation.dual ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embBar E n)) p.1
  map_one' := by
    rw [Prod.fst_one, map_one (Representation.dual _)]
    simp
  map_mul' p q := by
    rw [Prod.fst_mul, map_mul (Representation.dual _), smul_mul_smul_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Units.val_mul, det_mul, map_mul, map_mul, ← mul_zpow, mul_mul_mul_comm]

def jOf (W : Wt E n) (c : InfinitePlace E → ℤ) : ℤ := ∑ v, ((∑ i, (W v).w i) + n * c v)

structure IsFormG (x : E) (U : Submodule ℂ (UA E n → ℂ)) (W : Wt E n) (c : InfinitePlace E → ℤ) (w₀ : Plc E) (J : Subgroup (GLw n w₀)) (χ : J →* ℂˣ)
    (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)) (Φ : GUf E n → Module.Dual ℂ W.Sp) (κ : HChar E) : Prop where
  ne : Φ ≠ 0
  left : ∀ (γ : Gam0 E n) g, Φ (rat γ * g) = xiG W c γ.1 (Φ g)
  right : ∀ k ∈ lev S Kw, ∀ h : invT n _ (comp w₀ k) ∈ J, ∀ g, Φ (g * k) = ((χ ⟨_, h⟩ : ℂˣ) : ℂ) • Φ g
  sat : ∀ (w : Plc E) (hw : IsSplitAt w), w ∉ S → cj w ∉ S → ∀ B, SatU U w B →
    IsSatVecGL w (((rightReg ℂ (GUf E n) (Module.Dual ℂ W.Sp)).comp (loc hw)).comp (invT n _)) Φ B
  alg : IsAlgPos κ (mOf x W (jOf W c))
  unr : ∀ w : Plc E, (∀ u ∈ S, ¬ SameK x (cj u) w) → κ.UnrAt w
  cen : ∀ w : Plc E, (∀ u ∈ S, ¬ SameK x (cj u) w) → ¬ SameK x (cj w) w → ∀ z, IsCen x w z →
    ∀ g, Φ (g * z⁻¹) = ((κ.val w : ℂˣ) : ℂ)⁻¹ • Φ g

def SeedG : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 0 < n → ∀ (d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) →
  ∀ (π : AutSub E n) (W : Wt E n), π.finPart W ≠ ⊥ → ∀ (c : InfinitePlace E → ℤ) (Up : Plc E → Prop), (∀ w, IsSplitAt w → Up w ∨ Up (cj w)) →
  ∀ w₀ : Plc E, IsSplitAt w₀ → Up w₀ → ∀ (J : Subgroup (GLw n w₀)) (χ : J →* ℂˣ), IsOpen (J : Set (GLw n w₀)) →
    IsCompact (J : Set (GLw n w₀)) → HasType π.V w₀ J χ →
  ∃ (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)) (Φ : GUf E n → Module.Dual ℂ W.Sp) (κ : HChar E),
    Shape Up w₀ S Kw ∧ Kw w₀ = J.comap (invT n _) ∧ IsOpen {k : J | χ k = 1} ∧ IsOpen (lev S Kw : Set (GUf E n)) ∧
    IsCompact (lev S Kw : Set (GUf E n)) ∧
    (∀ w, IsSplitAt w → Apart w w₀ → (∃ B, SatU π.V w B) → w ∉ S ∧ cj w ∉ S) ∧ IsFormG x π.V W c w₀ J χ S Kw Φ κ

def XiTh : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (c : InfinitePlace E → ℤ) (γ : Gam0 E n),
  xi0 W (jOf W c) (th0 γ) = xiG W c γ.1

def ThLoc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
  (∀ (w : Plc E) (hw : IsSplitAt w) (y : GLw n w), th (loc hw y) = loc hw (invT n _ y)) ∧
    (0 < n → ∀ (x : E) (w : Plc E) (z : GUf E n), IsCen x w z → th z = z⁻¹)

theorem seedG_of (h0 : SeedGU) (h1 : XiTh) (h2 : ThLoc) (h3 : LevOpen) (h4 : LevCompact) : SeedG := by
  intro E _ _ _ n hn d x hd hx π W hW c Up hUp w₀ hw₀ hu J χ hJo hJc hT
  obtain ⟨S, Kw, Φ, κ, hS, hJ, hχ, -, -, hsph, hΦ, hκ⟩ := h0 E n hn d x hd hx π W hW (jOf W c) Up hUp w₀ hw₀ hu J χ hJo hJc hT
  have hS' : Shape Up w₀ S (levT Kw) := by
    refine ⟨hS.mem, fun w hw => (hS.opn w hw).preimage (GlobalTheory.SplitPts.continuous_invT _), fun w hw => ?_, fun w hw hne y hy => ?_, hS.up⟩
    · convert (hS.cpt w hw).image (GlobalTheory.SplitPts.continuous_invT (n := n) _) using 1
      ext y
      exact ⟨fun h => ⟨_, h, invT_invT' y⟩, fun ⟨z, hz, e⟩ => e ▸ (show invT n _ (invT n _ z) ∈ Kw w by rwa [invT_invT'])⟩
    · simpa using invT_mem_KGL (hS.le w hw hne hy)
  refine ⟨S, levT Kw, fun g => Φ (th g), κ, hS', by rw [levT, hJ], hχ, h3 E n S _ hS'.opn, h4 E n Up w₀ hw₀ S _ hS', hsph,
    fun h => hΦ.ne (funext fun g => by simpa using congrFun h (th g)), fun γ g => ?_, fun k hk h g => ?_, fun w hw a b B hB => ?_,
    hκ.alg, hκ.unr, fun w a b z hz g => ?_⟩
  · rw [map_mul, th_rat, hΦ.left, h1]
  · have h' : comp w₀ (th k) ∈ J := by rwa [comp_th]
    rw [map_mul, hΦ.right _ (th_mem_lev.2 hk) h']
    congr 3
  · obtain ⟨s1, s2, s3, s4⟩ := hΦ.sat w hw a b B hB
    let L : (GUf E n → Module.Dual ℂ W.Sp) ≃ₗ[ℂ] (GUf E n → Module.Dual ℂ W.Sp) :=
      LinearEquiv.funCongrLeft ℂ _ ⟨th, th, th_th, th_th⟩
    have hL : ∀ y Ψ, L (((rightReg ℂ (GUf E n) (Module.Dual ℂ W.Sp)).comp (loc hw)) y Ψ) =
        (((rightReg ℂ (GUf E n) (Module.Dual ℂ W.Sp)).comp (loc hw)).comp (invT n _)) y (L Ψ) := fun y Ψ => funext fun g => by
      show Ψ (th g * loc hw y) = Ψ (th (g * loc hw (invT n _ y)))
      rw [map_mul, (h2 E n).1, invT_invT']
    refine ⟨fun h => s1 (L.map_eq_zero_iff.1 h), GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, s3, fun p hp i hi => ?_⟩
    · exact (hL k Φ).symm.trans (congrArg L (GlobalTheory.LGrp.mem_fixed.1 s2 k hk))
    · have e := congrArg L (s4 p hp i hi)
      rw [map_smul] at e
      refine Eq.trans ?_ e
      unfold heckeVec
      rw [show L (∑ᶠ c, _) = _ from L.toAddEquiv.map_finsum _]
      refine finsum_congr fun c => ?_
      exact ((congrArg _ (hL _ Φ)).symm.trans (L.map_smul _ _).symm)
  · rw [map_mul, map_inv, (h2 E n).2 hn x w z hz, inv_inv, hκ.cen w a b z hz]

end UpperTheory.Gal.CertificateRingHomMap

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCentralEig2Of
section
open Module

private theorem exists_common_eigenvector_of_commute_of_invariant {E ι : Type} [AddCommGroup E] [Module ℂ E]
    (T : ι → E →ₗ[ℂ] E) (hT : ∀ i j, T i ∘ₗ T j = T j ∘ₗ T i) :
    ∀ n : ℕ, ∀ W : Submodule ℂ E, finrank ℂ W = n → FiniteDimensional ℂ W → W ≠ ⊥ →
      (∀ i, ∀ x ∈ W, T i x ∈ W) → ∃ x ∈ W, x ≠ 0 ∧ ∀ i, ∃ c : ℂ, T i x = c • x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hfin hne hW
  by_cases hs : ∀ i, ∃ c : ℂ, ∀ x ∈ W, T i x = c • x
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨x, hx, hx0, fun i => (hs i).imp fun c hc => hc x hx⟩
  · push_neg at hs
    obtain ⟨i, hi⟩ := hs
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((T i).restrict (fun x hx => hW i x hx))
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    set W' : Submodule ℂ E := W ⊓ LinearMap.ker (T i - μ • LinearMap.id) with hW'
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ T i x = μ • x := by
      intro x
      simp [hW', sub_eq_zero]
    have hle : W' ≤ W := inf_le_left
    have hlt : W' < W := by
      refine lt_of_le_of_ne hle ?_
      intro heq
      obtain ⟨x, hx, hne'⟩ := hi μ
      exact hne' ((hmem x).1 (by rw [heq]; exact hx)).2
    haveI : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le hle
    have hlt' : finrank ℂ W' < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hne' : W' ≠ ⊥ := by
      intro hbot
      have hv0 : (v : E) ∈ W' := (hmem _).2 ⟨v.2, by
        have := hv.apply_eq_smul
        simpa using congrArg Subtype.val this⟩
      rw [hbot, Submodule.mem_bot] at hv0
      exact hv.2 (Subtype.ext hv0)
    have hW'inv : ∀ j, ∀ x ∈ W', T j x ∈ W' := by
      intro j x hx
      rw [hmem] at hx ⊢
      refine ⟨hW j x hx.1, ?_⟩
      have h1 := LinearMap.congr_fun (hT i j) x
      simp only [LinearMap.comp_apply] at h1
      rw [h1, hx.2, map_smul]
    obtain ⟨x, hx, hx0, hc⟩ := ih _ hlt' W' rfl inferInstance hne' hW'inv
    exact ⟨x, hle hx, hx0, hc⟩

theorem UpperTheory.Gal.CertificateRingHomMap.pCentralEig2_of :
    UpperTheory.Gal.CertificateRingHomMap.CentralEig2 := by
  intro Γ H Z V _ _ _ _ _ ι K ξ ζ hζ M hfin hM hne hinv
  let T : Z → (H → V) →ₗ[ℂ] (H → V) := fun z =>
    { toFun := fun Φ g => Φ (g * ζ z), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hT : ∀ a b, T a ∘ₗ T b = T b ∘ₗ T a := by
    intro a b
    refine LinearMap.ext fun Φ => funext fun g => ?_
    show Φ (g * ζ a * ζ b) = Φ (g * ζ b * ζ a)
    rw [mul_assoc, mul_assoc, hζ a (ζ b)]
  obtain ⟨Φ, hΦM, hΦ0, hc⟩ :=
    exists_common_eigenvector_of_commute_of_invariant T hT _ M rfl hfin hne (fun z Φ hΦ => hinv Φ hΦ z)
  choose c hc using hc
  have hcg : ∀ z g, Φ (g * ζ z) = c z • Φ g := fun z g => congrFun (hc z) g
  obtain ⟨g0, hg0⟩ := Function.ne_iff.mp hΦ0
  have hscal : ∀ a b : ℂ, a • Φ g0 = b • Φ g0 → a = b := fun a b h =>
    smul_left_injective ℂ hg0 h
  have hF : (∀ (γ : Γ) (g : H), Φ (ι γ * g) = ξ γ (Φ g)) ∧ ∀ k ∈ K, ∀ g : H, Φ (g * k) = Φ g :=
    hM hΦM
  have h1 : c 1 = 1 := by
    apply hscal
    rw [← hcg 1 g0, map_one, mul_one, one_smul]
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    apply hscal
    rw [← hcg (a * b) g0, map_mul, ← mul_assoc, hcg b, hcg a, smul_smul, mul_comm]
  let χ : Z →* ℂ := { toFun := c, map_one' := h1, map_mul' := hmul }
  refine ⟨Φ, hΦM, hΦ0, χ.toHomUnits, ?_, ?_, ?_⟩
  · intro z g
    exact hcg z g
  · intro z hz
    apply Units.ext
    show c z = 1
    apply hscal
    rw [← hcg z g0, hF.2 _ hz g0, one_smul]
  · intro z γ a hzγ hξ
    show c z = a
    apply hscal
    rw [← hcg z g0, ← hξ (Φ g0), ← hF.1 γ g0, ← hzγ, hζ z g0]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PFinToHecke
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pFinToHecke_of :
    UpperTheory.Gal.CertificateRingHomMap.FinToHecke := by
  intro E _ _ ψ m ho hk
  obtain ⟨f, hf, hfe⟩ := exists_infPow_hom E m
  let p : Neutral.B1.Ideles E →* (Af E)ˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E) : _ →* _)
  have hpc : Continuous p := Continuous.units_map _ continuous_snd
  have hψ : Continuous ψ := continuous_of_isOpen_ker' ψ ho
  have hd : ∀ k : Eˣ, p (Neutral.B1.diagUnits E k) = diagF E k := fun k => Units.ext rfl
  have hl : ∀ (w : Plc E) y, p (Neutral.B1.localIdele E w y) = sgl w y := fun w y => Units.ext rfl
  have hi : ∀ k : Eˣ, p (infDiag k) = 1 := fun k => by
    rw [infDiag_eq]
    exact Units.ext rfl
  let θ : Neutral.B1.Ideles E →* ℂˣ := ψ.comp p * f
  have hθ : ∀ x, ((θ x : ℂˣ) : ℂ) = ((ψ (p x) : ℂˣ) : ℂ) * infPow m x := fun x => by
    rw [← hfe]
    rfl
  refine ⟨⟨θ, (hψ.comp hpc).mul hf, fun k => Units.ext ?_⟩, fun k _ => ?_, fun w y => ?_⟩
  · rw [hθ, hd, hk, infPow_diagUnits, Units.val_one]
    exact inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun φ _ => zpow_ne_zero _ (by simp))
  · show ((θ (infDiag k) : ℂˣ) : ℂ) = _
    rw [hθ, hi, infPow_infDiag, infPow_diagUnits, map_one, Units.val_one, one_mul]
  · show θ (Neutral.B1.localIdele E w y) = _
    refine Units.ext ?_
    rw [hθ, hl, infPow_localIdele, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntCompact
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem isCompact_ZU : IsCompact (ZU : Set AfQˣ) := by
  have hO := GroundTheory.Global.isCompact_integralFiniteAdeles ℚ
  have hB' : IsCompact (MulOpposite.unop ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ) : Set AfQᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hO
  have e : (ZU : Set AfQˣ) = Units.embedProduct _ ⁻¹'
      ((GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ) ×ˢ
        (MulOpposite.unop ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ))) := by
    ext s
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, MulOpposite.unop_op,
      GroundTheory.Global.mem_integralFiniteAdeles]
    constructor
    · intro h
      have h2 := (ZU.inv_mem h)
      exact ⟨fun v => (h v).le, fun v => (h2 v).le⟩
    · rintro ⟨h1, h2⟩ v
      have h3 : Valued.v ((s : AfQ) v) * Valued.v ((↑s⁻¹ : AfQ) v) = 1 := by
        rw [← map_mul]
        show Valued.v (((s : AfQ) * (↑s⁻¹ : AfQ)) v) = 1
        rw [Units.mul_inv]; exact map_one _
      refine le_antisymm (h1 v) ?_
      calc (1 : _) = Valued.v ((s : AfQ) v) * Valued.v ((↑s⁻¹ : AfQ) v) := h3.symm
        _ ≤ Valued.v ((s : AfQ) v) * 1 := mul_le_mul_right (h2 v) _
        _ = _ := mul_one _
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hO.prod hB')

private theorem isClosed_GUf (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    IsClosed (GUf E n : Set (GL (Fin n) (Af E) × AfQˣ)) := by
  have hl : Continuous fun p : GL (Fin n) (Af E) × AfQˣ =>
      (p.1.val.map (conjFin (GlobalTheory.SplitPts.conjE E)))ᵀ * p.1.val :=
    ((Units.continuous_val.comp continuous_fst).matrix_map (continuous_conjFin _)).matrix_transpose.matrix_mul
      (Units.continuous_val.comp continuous_fst)
  have hr : Continuous fun p : GL (Fin n) (Af E) × AfQˣ =>
      GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (p.2 : AfQ) • (1 : Matrix (Fin n) (Fin n) (Af E)) :=
    Continuous.smul (f := fun p : GL (Fin n) (Af E) × AfQˣ => GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (p.2 : AfQ))
      (g := fun _ => (1 : Matrix (Fin n) (Fin n) (Af E)))
      (GroundTheory.Global.AdeleBaseChange.continuous_finiteAdeleMap.comp (Units.continuous_val.comp continuous_snd))
      continuous_const
  exact isClosed_eq hl hr

theorem UpperTheory.Gal.CertificateRingHomMap.pIntCompact_of :
    UpperTheory.Gal.CertificateRingHomMap.IntCompact := by
  intro E _ _ _ n
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have e : Subtype.val '' (lev (E := E) (n := n) ∅ (fun _ => ⊤) : Set (GUf E n)) =
      (GUf E n : Set (GL (Fin n) (Af E) × AfQˣ)) ∩ ((GlobalTheory.EulerTw.Kglob E n : Set _) ×ˢ (ZU : Set AfQˣ)) := by
    ext p
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨h1, -, h3⟩ := mem_lev.1 hk
      exact ⟨k.2, GlobalTheory.EulerTwRestr.mem_Kglob.2 fun w => h3 w (by simp) (by simp), h1⟩
    · rintro ⟨hp, h1, h2⟩
      refine ⟨⟨p, hp⟩, mem_lev.2 ⟨h2, by simp, fun w _ _ => GlobalTheory.EulerTwRestr.mem_Kglob.1 h1 w⟩, rfl⟩
  rw [e]
  exact ((GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)).prod isCompact_ZU).inter_left (isClosed_GUf E n)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.POfUBij
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pOfUBij_of :
    UpperTheory.Gal.CertificateRingHomMap.OfUBij := by
  intro E _ _ _ n
  refine ⟨fun u v h => ?_, fun g hg => ?_⟩
  · have h1 : GeneralLinearGroup.map (pFin E) u.1.1 = GeneralLinearGroup.map (pFin E) v.1.1 :=
      congrArg (fun x : GUf E n => mat x) h
    have h2 := congrArg (finGL E n) h1
    rw [GlobalTheory.DefU.ClassFin.finGL_pFin, GlobalTheory.DefU.ClassFin.finGL_pFin] at h2
    exact Subtype.ext (Subtype.ext h2)
  · have hs : g.1.2 = 1 := hg
    have h : Formalism.UG.cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (mat g).val * (mat g).val = 1 :=
      (mem_Sim.1 g.2).trans (by rw [hs]; simp)
    refine ⟨⟨⟨finGL E n (mat g), GlobalTheory.DefU.ClassFin.finGL_mem_UA _ h⟩, pInf_finGL _⟩, ?_⟩
    exact Subtype.ext (Prod.ext (pFin_finGL _) hs.symm)
end

