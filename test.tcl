# Tool setup variables
set_fml_appmode AEP
set_app_var fml_mode_on true

# Read design file
# fill this section

# Declare clock/reset
# fill this section

# Save initial state
sim_run -stable
sim_save_reset
