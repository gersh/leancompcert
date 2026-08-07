import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk664

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471517645953203, 362471582808801161⟩, ⟨922191431092909572, 925113778081859044⟩, true⟩

def state01 : KState := ⟨⟨362476615697067978, 362476680880213897⟩, ⟨583737402544794461, 586661097421022039⟩, true⟩

def words00 : List Nat := [371285515036933338, 371285514993750918, 371285515005780286, 371285515126704171, 371285515219816694, 371285515222080941, 371285515012951257, 371285514921387359, 371285514828659959, 371285514807294473]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 66400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 66400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481182299915282, 362481247503691202⟩, ⟨280466712271660297, 283391777289088369⟩, true⟩

def words01 : List Nat := [371285514675984794, 371285514530408215, 371285514462318941, 371285514464814351, 371285514432311834, 371285514435842903, 371285514437544083, 371285514434926567, 371285514228433994, 371285514167004799]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 66410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 66400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474394635884655, 362474459859850756⟩, ⟨731338636633633179, 734265042787621777⟩, true⟩

def words02 : List Nat := [371285514243012447, 371285514245277190, 371285514083820308, 371285513876588182, 371285513668467850, 371285513527621145, 371285513272392992, 371285513225657854, 371285513178208021, 371285513074404236]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 66420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 66400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490432091916513, 362490497336369686⟩, ⟨(-334075125364333554), (-331147358152114000)⟩, true⟩

def words03 : List Nat := [371285512969444751, 371285513032077541, 371285513283394091, 371285513285659815, 371285513263855489, 371285513204615116, 371285513177641631, 371285513180161359, 371285513177282452, 371285513254881568]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 66430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 66400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470638202623925, 362470703467501089⟩, ⟨981068333993514629, 983997458279901097⟩, true⟩

def words04 : List Nat := [371285513331916210, 371285513334181832, 371285513130762587, 371285513030810914, 371285512929719508, 371285512864089832, 371285512496248802, 371285512107608773, 371285511718029153, 371285511555661810]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 66440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 66400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362460988525069619, 362461053810348550⟩, ⟨1622321691065766643, 1625252171152720695⟩, true⟩

def words05 : List Nat := [371285511334394022, 371285511139208845, 371285510943288714, 371285510719170212, 371285510213786699, 371285509779100542, 371285509343194280, 371285509134182138, 371285508767591379, 371285508402150427]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 66450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 66400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480667171213092, 362480732476777446⟩, ⟨314422883033030860, 317354711389392340⟩, true⟩

def words06 : List Nat := [371285508035734322, 371285507845048274, 371285507596898379, 371285507575777085, 371285507553964243, 371285507474877320, 371285507119154272, 371285506990643339, 371285506879587482, 371285506881943527]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 66460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 66400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474124426799928, 362474189753051993⟩, ⟨749385676287107049, 752318879861664605⟩, true⟩

def words07 : List Nat := [371285506811811177, 371285506742811852, 371285506717378971, 371285506719902424, 371285506652840735, 371285506653139859, 371285506652694470, 371285506653149717, 371285506389751018, 371285506222363992]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 66470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 66400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469450074393325, 362469515420830215⟩, ⟨1060192194415147536, 1063126739983718262⟩, true⟩

def words08 : List Nat := [371285506053683906, 371285506050877409, 371285505831148171, 371285505607852437, 371285505383699462, 371285505229960929, 371285504994280390, 371285504903027248, 371285504810992423, 371285504693502553]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 66480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 66400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483687368061897, 362483752735010335⟩, ⟨113467767092430803, 116403676574951679⟩, true⟩

def words09 : List Nat := [371285504454567838, 371285504442668102, 371285504457004058, 371285504459271433, 371285504187211808, 371285503882571941, 371285503576987854, 371285503440573821, 371285503189981288, 371285503166237027]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 66490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 66400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 66400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk664
