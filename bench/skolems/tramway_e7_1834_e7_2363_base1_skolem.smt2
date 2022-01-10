(declare-fun $~flatten0$2 () Bool)
(declare-fun $V276_X$2 () Bool)
(declare-fun $V274_X$2 () Bool)
(declare-fun $V61_close_door$2 () Bool)
(declare-fun $V273_X$2 () Bool)
(declare-fun $V60_open_door$2 () Bool)
(declare-fun $V271_warning_start_only_in_station$2 () Bool)
(declare-fun $V266_door_doesnt_open_if_not_asked$2 () Bool)
(declare-fun $V272_warning_start_cant_become_true_when_door_is_opening$2
             ()
             Bool)
(declare-fun $V270_warning_start_and_in_station_go_down_simultaneously$2
             ()
             Bool)
(declare-fun $V268_door_initially_closed$2 () Bool)
(declare-fun $door_is_open$0 () Bool)
(declare-fun $in_station$0 () Bool)
(declare-fun $V253_between_A_and_X$2 () Bool)
(declare-fun $V250_door_doesnt_open_out_of_station$2 () Bool)
(declare-fun $OK$2 () Bool)
(declare-fun $V59_prop_ok$2 () Bool)
(declare-fun $V265_door_doesnt_close_if_not_asked$2 () Bool)
(declare-fun $V252_X$~1 () Bool)
(declare-fun $V276_X$~1 () Bool)
(declare-fun $V251_door_opens_before_leaving_station$2 () Bool)
(declare-fun $V264_env_ok$2 () Bool)
(declare-fun $V275_X$2 () Bool)
(declare-fun $V252_X$2 () Bool)
(declare-fun $V58_env_always_ok$2 () Bool)
(declare-fun $V275_X$~1 () Bool)
(declare-fun $V269_initially_not_in_station$2 () Bool)
(declare-fun $V267_tramway_doesnt_start_if_not_door_ok$2 () Bool)
(declare-fun $warning_start$0 () Bool)

(assert (let ((a!1 (not (and (not $door_is_open$0)
                     (not $in_station$0)
                     (or (not $warning_start$0) $in_station$0))))
      (a!2 (= (ite true false (or (not $in_station$0) (not $V275_X$~1)))
              (ite true false (or (not $warning_start$0) (not $V276_X$~1)))))
      (a!4 (or false (ite true false (or (not $in_station$0) (not $V252_X$~1))))))
(let ((a!3 (and true
                (not $in_station$0)
                true
                (not $door_is_open$0)
                a!2
                (or $in_station$0 (not $warning_start$0))))
      (a!6 (= $V59_prop_ok$2
              (and (or $in_station$0 (not $door_is_open$0)) (not a!4)))))
(let ((a!5 (or (not a!3)
               (and (or $in_station$0 (not $door_is_open$0)) (not a!4)))))
(let ((a!7 (and (= $OK$2 a!5)
                (= $V58_env_always_ok$2 a!3)
                a!6
                (= $V264_env_ok$2 a!3)
                (= $V250_door_doesnt_open_out_of_station$2
                   (or $in_station$0 (not $door_is_open$0)))
                (= $V251_door_opens_before_leaving_station$2 (not a!4))
                (= $V253_between_A_and_X$2 false)
                (= $V252_X$2 (not $in_station$0))
                (= $V266_door_doesnt_open_if_not_asked$2 true)
                (= $V265_door_doesnt_close_if_not_asked$2 true)
                (= $V267_tramway_doesnt_start_if_not_door_ok$2 true)
                (= $V268_door_initially_closed$2 (not $door_is_open$0))
                (= $V269_initially_not_in_station$2 (not $in_station$0))
                (= $V270_warning_start_and_in_station_go_down_simultaneously$2
                   a!2)
                (= $V271_warning_start_only_in_station$2
                   (or $in_station$0 (not $warning_start$0)))
                (= $V272_warning_start_cant_become_true_when_door_is_opening$2
                   true)
                (= $V60_open_door$2 true)
                (= $V273_X$2 (not $door_is_open$0))
                (= $V61_close_door$2 true)
                (= $V274_X$2 (not $in_station$0))
                (= $V275_X$2 (not $in_station$0))
                (= $V276_X$2 (not $warning_start$0))
                (= $~flatten0$2 false))))
  (ite (or a!1 (not $door_is_open$0) $in_station$0) a!7 true))))))
(check-sat)