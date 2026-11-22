import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0002

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelCharts.LamHLocPrinc
section
noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

section Loc

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}

def HLoc (H : Subgroup (GL (Fin N) (resV F v))) : Subgroup (GL (Fin N) (v.adicCompletion F)) :=
  congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) H

def lamHLoc {Z : Type} [CommGroup Z] (H : Subgroup (GL (Fin N) (resV F v))) (lam : H →* Z) : HLoc F v H →* Z :=
  congChar _ (algMapV_injective F v) _ _ lam

theorem princ_le_HLoc (H : Subgroup (GL (Fin N) (resV F v))) :
    princ (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ≤ HLoc F v H :=
  princ_le_congPre _ _ _

theorem HLoc_le_range (H : Subgroup (GL (Fin N) (resV F v))) :
    HLoc F v H ≤ (bc (n := Fin N) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range := by
  rintro _ ⟨g, _, rfl⟩
  exact ⟨g, rfl⟩

theorem lamHLoc_princ {Z : Type} [CommGroup Z] (H : Subgroup (GL (Fin N) (resV F v))) (lam : H →* Z) (x : HLoc F v H)
    (hx : (x : GL (Fin N) (v.adicCompletion F)) ∈ princ (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))) : lamHLoc F v H lam x = 1 :=
  congChar_princ _ (algMapV_injective F v) _ _ lam x hx

theorem HLoc_mono {H H' : Subgroup (GL (Fin N) (resV F v))} (h : H ≤ H') : HLoc F v H ≤ HLoc F v H' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem JLoc_eq_HLoc (a t : ℕ) (fixLast : Bool) (fc : ℕ) :
    JLoc F v N a t fixLast fc = HLoc F v (JBar (resV F v) N a t fixLast fc) := rfl

end Loc

section Uni

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (v : HeightOneSpectrum (𝓞 F))
  (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) (fr : GL (Fin N) (v.adicCompletion F))

def HU (H : Subgroup (GL (Fin N) (resV F v))) : Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)) :=
  UPts σE J (v.adicCompletion F) ⊓ (HLoc F v H).comap (toFr v spl fr)

theorem mem_HU (H : Subgroup (GL (Fin N) (resV F v))) (x : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
    x ∈ HU σE J v spl fr H ↔ x ∈ UPts σE J (v.adicCompletion F) ∧
      fr⁻¹ * bc ((RingHom.fst _ _).comp spl.toRingHom) x * fr ∈ HLoc F v H := by
  rw [HU, Subgroup.mem_inf, Subgroup.mem_comap, toFr_apply]

theorem HU_mono {H H' : Subgroup (GL (Fin N) (resV F v))} (h : H ≤ H') : HU σE J v spl fr H ≤ HU σE J v spl fr H' :=
  inf_le_inf_left _ (Subgroup.comap_mono (HLoc_mono F v h))

def lamHU {Z : Type} [CommGroup Z] (H : Subgroup (GL (Fin N) (resV F v))) (lam : H →* Z) : HU σE J v spl fr H →* Z :=
  (lamHLoc F v H lam).comp (((toFr v spl fr).subgroupComap (HLoc F v H)).comp (Subgroup.inclusion inf_le_right))

theorem lamHU_apply {Z : Type} [CommGroup Z] (H : Subgroup (GL (Fin N) (resV F v))) (lam : H →* Z) (x : HU σE J v spl fr H)
    (g : GL (Fin N) (v.adicCompletionIntegers F))
    (hg : redGL (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) g ∈ H)
    (hx : toFr v spl fr (x : GL (Fin N) (E ⊗[F] v.adicCompletion F)) =
      bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g) :
    lamHU σE J v spl fr H lam x = lam ⟨_, hg⟩ := by
  have hm : bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g ∈ HLoc F v H := ⟨g, hg, rfl⟩
  rw [← congChar_apply (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) (algMapV_injective F v) _ _ _ g hg hm]
  show lamHLoc F v H lam _ = _
  unfold lamHLoc
  congr 1
  exact Subtype.ext hx

theorem lamHU_princ {Z : Type} [CommGroup Z] (H : Subgroup (GL (Fin N) (resV F v))) (lam : H →* Z) (x : HU σE J v spl fr H)
    (hx : toFr v spl fr (x : GL (Fin N) (E ⊗[F] v.adicCompletion F)) ∈
      princ (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))) : lamHU σE J v spl fr H lam x = 1 :=
  lamHLoc_princ F v H lam _ hx

theorem JU_eq_HU (a t : ℕ) (fixLast : Bool) (fc : ℕ) :
    JU σE J v spl fr a t fixLast fc = HU σE J v spl fr (JBar (resV F v) N a t fixLast fc) := rfl

theorem lamU_eq_lamHU {Z : Type} [CommGroup Z] (a t : ℕ) (fixLast : Bool) (fc : ℕ) (ψ0 : AddChar (resV F v) Z)
    (χ : ℕ → (resV F v)ˣ →* Z) (Sd : Finset ℕ) (nb : ℕ) :
    lamU σE J v spl fr a t fixLast fc ψ0 χ Sd nb =
      lamHU σE J v spl fr (JBar (resV F v) N a t fixLast fc) (lamBar (resV F v) N a t fixLast fc ψ0 χ Sd nb) := rfl

end Uni

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

structure LevAtGH (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (gp : Fin 2 → ℕ)
    (splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (Lb : Submodule (𝓞 E) (Fin N → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))
    (H : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin N) (resV F v))) where

  frG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → GL (Fin N) (v.adicCompletion F)

  frG_lat : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (x : Fin N → v.adicCompletion F),
    (∃ y ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb,
      ∀ b, (splitG i v h (y b)).1 = x b) ↔
      ∀ b, (((frG i v h)⁻¹ : GL (Fin N) (v.adicCompletion F)) : Matrix (Fin N) (Fin N) (v.adicCompletion F)).mulVec x b ∈
        v.adicCompletionIntegers F

  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
    Uloc v = HU σE J v (splitG i v h) (frG i v h) (H i v h)

variable {σE : E →ₐ[F] E} {J : Matrix (Fin N) (Fin N) E} {gp : Fin 2 → ℕ}
    {splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    {Lb : Submodule (𝓞 E) (Fin N → E)}
    {Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))}
    {H : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin N) (resV F v))}
    {Z : Type} [CommGroup Z]

def LevAtG.toH {k m t j : ℕ} (X : LevAtG σE J gp splitG Lb Uloc k m t j) :
    LevAtGH σE J gp splitG Lb Uloc (fun _ v _ => JXbar (resV F v) N k m t j) where
  frG := X.frG
  frG_lat := X.frG_lat
  Uloc_g := X.Uloc_g

def LevAtGH.lamV (X : LevAtGH σE J gp splitG Lb Uloc H) (lam : ∀ i v h, H i v h →* Z) (i : Fin 2)
    (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) : Uloc v →* Z :=
  (lamHU σE J v (splitG i v h) (X.frG i v h) (H i v h) (lam i v h)).comp (Subgroup.inclusion (le_of_eq (X.Uloc_g i v h)))

def LevAtGH.lamGlob (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z)
    (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hUp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      Up ≤ (Uloc v).comap (bc (prV (E := E) v))) : Up →* Z :=
  ∏ i : Fin 2, prodChar (placesOver F (gp i)) Uloc
    (fun v hv => X.lamV lam i v ((mem_placesOver F (gp i) (hg i) v).1 hv))
    Up (fun v hv => hUp i v ((mem_placesOver F (gp i) (hg i) v).1 hv))

theorem LevAtGH.lamGlob_apply (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z)
    (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hUp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      Up ≤ (Uloc v).comap (bc (prV (E := E) v))) (x : Up) :
    X.lamGlob hg lam Up hUp x = ∏ i : Fin 2, ∏ v ∈ (placesOver F (gp i)).attach,
      X.lamV lam i v.1 ((mem_placesOver F (gp i) (hg i) v.1).1 v.2)
        ⟨bc (prV (E := E) v.1) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
          hUp i v.1 ((mem_placesOver F (gp i) (hg i) v.1).1 v.2) x.2⟩ := by
  simp only [LevAtGH.lamGlob, MonoidHom.finsetProd_apply, prodChar_apply]

theorem LevAtG.toH_lamGlob {k m t j : ℕ} (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0)
    (ψ0 : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → AddChar (resV F v) Z)
    (χ : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ℕ → (resV F v)ˣ →* Z)
    (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hUp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      Up ≤ (Uloc v).comap (bc (prV (E := E) v))) :
    X.toH.lamGlob hg (fun i v h => lamXbar (resV F v) N k m t j (ψ0 i v h) (χ i v h)) Up hUp = X.lamGlob hg ψ0 χ Up hUp := rfl

def LevAtGH.lamG (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z :=
  X.lamGlob hg lam (awayG σE J Uloc p) (fun i v h => awayG_le_comap p v (not_mem_of_coprime (hp i) v h))

def LevAtGH.typeX (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z := (X.lamG hg lam p hp)⁻¹

def LevAtGH.psiX (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z := (X.typeX hg lam p hp)⁻¹

theorem LevAtGH.psiX_eq (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : X.psiX hg lam p hp = X.lamG hg lam p hp := inv_inv _

def CharsG.lamX (ch : CharsG F gp Z) (N k m t j : ℕ) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) :
    JXbar (resV F v) N k m t j →* Z := lamXbar (resV F v) N k m t j (ch.psi0 i v h) (ch.chi i v h)

theorem LevAtG.toH_typeX {k m t j : ℕ} (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0) (ch : CharsG F gp Z)
    (p : ℕ) (hp : ∀ i, Nat.Coprime p (gp i)) : X.toH.typeX hg (ch.lamX N k m t j) p hp = X.typeX hg ch p hp := rfl

theorem LevAtGH.princ_le (X : LevAtGH σE J gp splitG Lb Uloc H) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F))
    (h : (gp i : 𝓞 F) ∈ v.asIdeal) : HU σE J v (splitG i v h) (X.frG i v h) ⊥ ≤ Uloc v := by
  rw [X.Uloc_g i v h]
  exact HU_mono σE J v _ _ (_root_.bot_le)

theorem LevAtGH.le_top (X : LevAtGH σE J gp splitG Lb Uloc H) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F))
    (h : (gp i : 𝓞 F) ∈ v.asIdeal) : Uloc v ≤ HU σE J v (splitG i v h) (X.frG i v h) ⊤ := by
  rw [X.Uloc_g i v h]
  exact HU_mono σE J v _ _ (_root_.le_top)

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelsOfTie
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
  {L : ColLevel R F E sp gp C A clsLat}

structure GStepTie {p : ℕ} {G : GAtP p} (X : Formalism.L2.Herm.GLevTie L G) {Fl : Fills G} (Lv : Levels Fl) (i : ℕ) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (Lb : Submodule (𝓞 E) (Fin N → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))
    (ψ : awayG sp.cm.sig J Uloc p →* G.Oˣ) (eps : UJ (sp.cm.sig : E →+* E) J →* G.Oˣ) where

  rk : (Fl.Pj (i + 1)).m + 1 = N

  fr : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → GL (Fin N) (w.adicCompletion F)
  fr_lat : ∀ w h (t : Fin N → w.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL w Lb, ∀ a, (X.spl w h (x a)).1 = t a) ↔
      ∀ a, (((fr w h)⁻¹ : GL (Fin N) (w.adicCompletion F)) :
        Matrix (Fin N) (Fin N) (w.adicCompletion F)).mulVec t a ∈ w.adicCompletionIntegers F

  yG : Lv.compS i → UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F)
  yG_p : ∀ c (w : HeightOneSpectrum (𝓞 F)), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
    bc (prV (E := E) w) (yG c : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1
  yG_bij : Function.Bijective (fun c : Lv.compS i => (Quotient.mk'' (yG c) : compG sp.cm.sig J Uloc p))

  gamI : ∀ c, (Lv.levS i c).Γ →* UJ (sp.cm.sig : E →+* E) J
  gamI_inj : ∀ c, Function.Injective (gamI c)
  gamI_range : ∀ c (γ : UJ (sp.cm.sig : E →+* E) J), γ ∈ (gamI c).range ↔
    bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin N) E) ∈
      (awayG sp.cm.sig J Uloc p).map (MulAut.conj (yG c : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).toMonoidHom

  act_eq : ∀ c (v : Fin G.P.nV) w (h : (X.pl v).1 = w) (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (γ : (Lv.levS i c).Γ)
    (a b : Fin ((Fl.Pj (i + 1)).m + 1)) (a' b' : Fin N), (a : ℕ) = a' → (b : ℕ) = b' →
    X.eQ v w h (((Lv.levS i c).act v γ : GL (Fin ((Fl.Pj (i + 1)).m + 1)) (G.P.Qq v)) a b) =
      (((fr w hw)⁻¹ * bc ((RingHom.fst _ _).comp (X.spl w hw).toRingHom)
        (bc (inclE (F := F) (w.adicCompletion F)) (gamI c γ : GL (Fin N) E)) * fr w hw :
          GL (Fin N) (w.adicCompletion F)) : Matrix (Fin N) (Fin N) (w.adicCompletion F)) a' b'

  chi_eq : ∀ c (γ : (Lv.levS i c).Γ) (x : awayG sp.cm.sig J Uloc p),
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      (yG c : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))⁻¹ *
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gamI c γ : GL (Fin N) E) * yG c →
    (Lv.levS i c).χ γ = ψ x * eps (gamI c γ)

variable {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
  {n' : ℕ} {O Kf : Type} [IsDomain W] [IsDiscreteValuationRing W]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}

set_option maxHeartbeats 2000000 in

def levelsOf_tie (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F)) [Finite (compL L p)] (e : ℕ)
    (hy : ∀ i, (Quotient.mk'' (y i) : compL L p) = i)
    (hyp : ∀ i (w' : HeightOneSpectrum (𝓞 F)), ((p : ℕ) : 𝓞 F) ∈ w'.asIdeal →
      bc (prV (E := E) w') (y i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (Fl : Fills (gatOfLevel L hS nV r lam0 dom hk I ψ y e)) (M : ℕ) (Nj : ℕ → ℕ)
    (hN : ∀ i, i < M → m + (i + 1) * (Fl.t + 1) + 1 = Nj i) (St : ∀ i, i < M → StepAt I O (Nj i)) (i : ℕ) (hi : i < M) :
    GStepTie (gatOfLevel_tie L hS nV r lam0 dom hk I ψ y e hy hyp)
      (levelsOf hS r lam0 dom hk I ψ y e Fl M Nj hN St) i (St i hi).J (St i hi).Lb (St i hi).Uloc (St i hi).ψ (St i hi).eps where
  rk := hN i hi
  fr := (St i hi).fr.fr
  fr_lat := (St i hi).fr.fr_lat
  yG := fun c => (St i hi).rep c.2
  yG_p := fun c w' h => repG_over sp.cm.sig (St i hi).J (St i hi).Uloc p c.2 w' h
  yG_bij := ⟨fun a b hab => by
      obtain ⟨ha, a⟩ := a
      obtain ⟨hb, b⟩ := b
      have h1 := repG_mk sp.cm.sig (St i hi).J (St i hi).Uloc p a
      have h2 := repG_mk sp.cm.sig (St i hi).J (St i hi).Uloc p b
      have : a = b := by rw [← h1, ← h2]; exact hab
      subst this; rfl,
    fun c => ⟨⟨hi, c⟩, repG_mk sp.cm.sig (St i hi).J (St i hi).Uloc p c⟩⟩
  gamI := fun c => (gamC sp.cm.sig (St i hi).J (St i hi).Up
    ((St i hi).rep c.2 : GL (Fin (Nj i)) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).subtype
  gamI_inj := fun c => Subtype.val_injective
  gamI_range := by
    intro c γ
    constructor
    · rintro ⟨g, rfl⟩
      exact g.2
    · intro h
      exact ⟨⟨γ, h⟩, rfl⟩
  act_eq := by
    intro c v w' h hw γ a b a' b' ha hb
    subst h
    have h1 := levC_act sp.cm.sig (St i hi).J (St i hi).Up hS nV r
      (fun v s => liftWt Fl.t m (lam0 v s) (fun a => Fl.w v a s) (i + 1)) (Fl.domJ (i + 1)) (hN i hi) I.iw (St i hi).fr.frQ
      (St i hi).ψ ((St i hi).rep c.2 : GL (Fin (Nj i)) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) v γ
    have h2 : ∀ g : GL (Fin (m + (i + 1) * (Fl.t + 1) + 1)) Qq,
        (g : Matrix (Fin (m + (i + 1) * (Fl.t + 1) + 1)) (Fin (m + (i + 1) * (Fl.t + 1) + 1)) Qq) a b =
        (castGL (hN i hi) Qq g : Matrix (Fin (Nj i)) (Fin (Nj i)) Qq) a' b' := by
      intro g
      rw [castGL_apply]
      have ea : a = Fin.cast (hN i hi).symm a' := Fin.ext ha
      have eb : b = Fin.cast (hN i hi).symm b' := Fin.ext hb
      rw [ea, eb]
    have h3 : ((St i hi).fr.frQ v)⁻¹ * bc (I.iw v) (gamMat sp.cm.sig (St i hi).J (St i hi).Up
          ((St i hi).rep c.2 : GL (Fin (Nj i)) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) γ) * (St i hi).fr.frQ v =
        bc (I.eQ v).symm.toRingHom (((St i hi).fr.fr (I.pl v).1 (I.pl v).2)⁻¹ *
          bc ((RingHom.fst _ _).comp (I.spl (I.pl v).1 (I.pl v).2).toRingHom)
            (bc (inclE (F := F) ((I.pl v).1.adicCompletion F)) (gamMat sp.cm.sig (St i hi).J (St i hi).Up
              ((St i hi).rep c.2 : GL (Fin (Nj i)) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) γ)) *
                (St i hi).fr.fr (I.pl v).1 (I.pl v).2) := by
      rw [map_mul, map_mul, map_inv]
      rfl
    show I.eQ v _ = _
    rw [h2 (((levelsOf hS r lam0 dom hk I ψ y e Fl M Nj hN St).levS i c).act v γ)]
    erw [h1]
    rw [h3]
    show I.eQ v ((I.eQ v).symm _) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  chi_eq := by
    intro c γ x hx
    show (St i hi).ψ (gamToUp sp.cm.sig (St i hi).J (St i hi).Up
      ((St i hi).rep c.2 : GL (Fin (Nj i)) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) γ) * (St i hi).eps γ.1 =
        (St i hi).ψ x * (St i hi).eps γ.1
    congr 2
    apply Subtype.ext
    rw [hx]
    show (MulAut.conj ((St i hi).rep c.2 : GL (Fin (Nj i)) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))⁻¹) _ = _
    rw [MulAut.conj_apply, inv_inv]
    rfl

end Formalism.L2.G
end
end

