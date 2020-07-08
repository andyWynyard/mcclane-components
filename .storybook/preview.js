import { addDecorator, configure } from '@storybook/react'
import { ThemeProvider } from 'styled-components'
import React from 'react'
import { Router } from 'react-router-dom'
import { createBrowserHistory } from 'history'

import { defaultTheme } from '../src/defaultTheme'

const history = createBrowserHistory()

addDecorator((story) => {
  // console.log('defaultTheme', defaultTheme)
  return (
    <ThemeProvider theme={defaultTheme}>
      <Router history={history}>{story()}</Router>
    </ThemeProvider>
  )
})

export const parameters = {
  actions: { argTypesRegex: '^on.*' },
}
