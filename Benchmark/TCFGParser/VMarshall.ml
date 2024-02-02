open Core

let marshall name v =
  Marshal.to_channel
    (Out_channel.create ?binary:(Some true) ?append:(Some false)
        ?fail_if_exists:(Some false) name)
    v []