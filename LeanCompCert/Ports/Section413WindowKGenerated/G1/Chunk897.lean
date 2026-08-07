import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk897

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485627219991597, 362485748940813365⟩, ⟨(-62205761074744615), (-54833826162161167)⟩, true⟩

def state01 : KState := ⟨⟨362475554637042223, 362475676385672854⟩, ⟨841374733326269121, 848749162842802599⟩, true⟩

def words00 : List Nat := [371285137767276464, 371285137770405301, 371285137727086465, 371285137685406047, 371285137642553363, 371285137582282802, 371285137458710913, 371285137450100069, 371285137440465603, 371285137417473577]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 89700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 89700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487528154671430, 362487649931674478⟩, ⟨(-232816941168565397), (-225439966223886255)⟩, true⟩

def words01 : List Nat := [371285137326590422, 371285137342936448, 371285137418213942, 371285137421345679, 371285137356237658, 371285137272467202, 371285137211949289, 371285137215405713, 371285137222308890, 371285137253859654]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 89710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 89700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481800210499537, 362481922015771603⟩, ⟨281074810468482492, 288454321852892722⟩, true⟩

def words02 : List Nat := [371285137282656256, 371285137285786055, 371285137164591397, 371285137111656480, 371285137057212135, 371285137015687446, 371285136928582691, 371285136819715439, 371285136709531609, 371285136707868482]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 89720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 89700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474014312034559, 362474136145482188⟩, ⟨979775158488668425, 987157198214406079⟩, true⟩

def words03 : List Nat := [371285136743229310, 371285136815660224, 371285136863471798, 371285136866602021, 371285136748736862, 371285136658622670, 371285136566863371, 371285136567464704, 371285136456158424, 371285136337127101]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 89730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 89700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473332059100817, 362473453920545341⟩, ⟨1041057921785198544, 1048442474094964552⟩, true⟩

def words04 : List Nat := [371285136216673544, 371285136200064895, 371285136120222655, 371285136120083124, 371285136118928516, 371285136109385528, 371285135964851947, 371285135873396193, 371285135780329183, 371285135730841664]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 89740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 89700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362478800443697828, 362478922333716236⟩, ⟨550258501141621751, 557645618095851553⟩, true⟩

def words05 : List Nat := [371285135603023705, 371285135476116792, 371285135347893664, 371285135345113719, 371285135295445345, 371285135270359758, 371285135244260106, 371285135219535370, 371285135028401705, 371285134963151351]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 89750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 89700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471412434456657, 362471534352368033⟩, ⟨1213435614340970609, 1220825235115480555⟩, true⟩

def words06 : List Nat := [371285134896098728, 371285134881510445, 371285134721859034, 371285134563049796, 371285134403083217, 371285134266666075, 371285134066561559, 371285133991843362, 371285133915983710, 371285133831426912]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 89760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 89700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484306498876052, 362484428445047349⟩, ⟨55850457132005285, 63242614942073685⟩, true⟩

def words07 : List Nat := [371285133682074145, 371285133597608148, 371285133535357496, 371285133538489100, 371285133399449074, 371285133239511177, 371285133078263786, 371285132996737702, 371285132867035105, 371285132862678694]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 89770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 89700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479085697052030, 362479207671492126⟩, ⟨524616643740305257, 532011339664604247⟩, true⟩

def words08 : List Nat := [371285132857173526, 371285132852358262, 371285132836405244, 371285132893166484, 371285132986160801, 371285132989292659, 371285132917129627, 371285132844651031, 371285132770964772, 371285132733744767]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 89780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 89700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475697770985094, 362475819773667890⟩, ⟨828872146513024066, 836269378490589266⟩, true⟩

def words09 : List Nat := [371285132686402409, 371285132706362570, 371285132708741899, 371285132702928286, 371285132601901751, 371285132540311899, 371285132535625087, 371285132538758279, 371285132450417936, 371285132350265781]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 89790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 89700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 89700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk897
