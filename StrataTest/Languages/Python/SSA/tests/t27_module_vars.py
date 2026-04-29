# Test: Module-level variable assignments visible to functions
# Module-level assignments like 'x = 1' in module M should be
# treated as globals accessible via qualifiedRef M.x in functions.

import logging

# Simple module-level assignments
MAX_RETRIES = 3
logger = logging.getLogger(__name__)

# Annotated assignment
threshold: float = 0.5

def use_module_vars():
    """Functions see module-level vars as qualifiedRef."""
    logger.info("starting")
    for i in range(MAX_RETRIES):
        if i > threshold:
            break

def param_shadows_module_var(logger):
    """Function parameter shadows module-level var of same name."""
    logger.info("param wins")

def local_shadows_module_var():
    """Local assignment shadows module-level var after the assignment."""
    MAX_RETRIES = 10
    return MAX_RETRIES

def mixed_imports_and_vars():
    """Function uses both imports and module-level vars."""
    new_logger = logging.getLogger("other")
    new_logger.setLevel(MAX_RETRIES)
