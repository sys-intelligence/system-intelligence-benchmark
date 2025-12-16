window.dash_clientside = Object.assign({}, window.dash_clientside, {
  utils: Object.assign({}, (window.dash_clientside || {}).utils, {
    scrollToBottom: function(triggerValue) {
      try {
        // Only scroll if triggerValue is True (new log arrived)
        if (triggerValue === true) {
          var container = document.getElementById('rows-display');
          if (container) {
            container.scrollTop = container.scrollHeight;
          }
        }
      } catch (e) {}
      return Date.now();
    }
  })
});

