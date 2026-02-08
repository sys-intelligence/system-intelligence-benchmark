#####################################################################
# CS:APP Proxy Lab
# Directions to Instructors
#
# Copyright (c) 2004-2016, R. Bryant and D. O'Hallaron, All rights reserved.
######################################################################

************
1. Overview
************

In this lab, students build a simple concurrent caching Web proxy that
accepts HTTP 1.0 requests from clients, forwards them to end servers,
and then sends the replies back to the clients.  The proxy caches
objects returned by the end servers, and attempts to satisfy requests
from clients from the cache before forwarding the requests to the end
servers.