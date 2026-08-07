import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk120

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502978673996245, 362502980516820427⟩, ⟨(-221991502132770907), (-221976536271390487)⟩, true⟩

def state01 : KState := ⟨⟨362468250776967025, 362468252622959799⟩, ⟨194964198694731875, 194979202595767643⟩, true⟩

def words00 : List Nat := [371284489132720212, 371284489133077038, 371284487265121994, 371284485408701995, 371284483552463648, 371284482039631753, 371284481241205611, 371284484295136888, 371284487360526181, 371284487360894501]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 12000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 12000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362525679439729574, 362525681288945229⟩, ⟨(-494742350179103716), (-494727307555156628)⟩, true⟩

def words01 : List Nat := [371284491560507889, 371284497111043806, 371284507931072143, 371284509546701630, 371284509900471716, 371284510254294865, 371284516447399711, 371284519186000475, 371284522610715557, 371284526035010020]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 12010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 12000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362431545406801211, 362431547259233583⟩, ⟨636918883744680916, 636933965050162292⟩, true⟩

def words02 : List Nat := [371284529472034704, 371284529472391259, 371284523719050682, 371284521545366654, 371284519371864045, 371284517824975603, 371284510558396213, 371284502993374686, 371284495429470242, 371284492725987545]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 12020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 12000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362427766385778799, 362427768241435266⟩, ⟨682625653464800770, 682640773572282900⟩, true⟩

def words03 : List Nat := [371284489377868054, 371284490430476344, 371284490430750756, 371284490236719858, 371284483903924740, 371284478784122326, 371284475416514429, 371284475416873269, 371284470689198938, 371284465980104061]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 12030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 12000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362513682554327161, 362513684413180227⟩, ⟨(-351918402350025623), (-351903243738933795)⟩, true⟩

def words04 : List Nat := [371284463430162603, 371284463430559750, 371284467885601500, 371284473545217666, 371284477500559315, 371284477500917467, 371284474462592125, 371284474297036839, 371284480824117972, 371284483247821425]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 12040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 12000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362518678915875589, 362518680777985354⟩, ⟨(-412025191825402191), (-412009993954576033)⟩, true⟩

def words05 : List Nat := [371284485486491501, 371284487724903569, 371284494260269105, 371284498438980156, 371284504750249766, 371284511060614163, 371284517394930233, 371284517395287854, 371284517428127708, 371284520261116556]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 12050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 12000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362438669096771881, 362438670962075061⟩, ⟨553309125161710085, 553324361561519737⟩, true⟩

def words06 : List Nat := [371284525966577236, 371284525966935140, 371284524014144433, 371284522091911528, 371284520169854816, 371284519593390065, 371284515578391542, 371284515129086271, 371284514679735000, 371284513908351907]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 12060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 12000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362561968152398444, 362561970020941542⟩, ⟨(-935435407111109651), (-935420131589021251)⟩, true⟩

def words07 : List Nat := [371284513142548901, 371284516174206019, 371284526032923074, 371284526781438959, 371284526781721906, 371284525482052698, 371284527312128298, 371284528168185171, 371284534579178338, 371284540989272887]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 12070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 12000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362458501958576932, 362458503830356186⟩, ⟨315062701960435727, 315078016591895231⟩, true⟩

def words08 : List Nat := [371284547428820469, 371284548187992798, 371284554496521835, 371284560804188034, 371284569239520427, 371284569239878887, 371284568586597359, 371284567185135604, 371284565783763628, 371284564873912175]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 12080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 12000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362407105158400912, 362407107033411865⟩, ⟨937003202183729261, 937018555902162635⟩, true⟩

def words09 : List Nat := [371284566572620543, 371284570426241670, 371284573810416076, 371284573810774987, 371284568118749625, 371284562737642026, 371284558774551170, 371284558774910682, 371284552983575720, 371284546583486424]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 12090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 12000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 12000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk120
